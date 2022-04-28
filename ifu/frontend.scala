//******************************************************************************
// Copyright (c) 2017 - 2019, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE and LICENSE.SiFive for license details.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// Frontend
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

package boom.ifu

import chisel3._
import chisel3.util._
import chisel3.internal.sourceinfo.{SourceInfo}

import freechips.rocketchip.config._
import freechips.rocketchip.subsystem._
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.rocket._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.tile._
import freechips.rocketchip.util._
import freechips.rocketchip.util.property._

import boom.common._
import boom.exu.{CommitExceptionSignals, BranchDecode, BrUpdateInfo, BranchDecodeSignals}
import boom.util._


class FrontendResp(implicit p: Parameters) extends BoomBundle()(p) {
  val pc = UInt(vaddrBitsExtended.W)  // ID stage PC
  val data = UInt((fetchWidth * coreInstBits).W)
  val mask = UInt(fetchWidth.W)
  val xcpt = new FrontendExceptions
  val ghist = new GlobalHistory

  // fsrc provides the prediction FROM a branch in this packet
  // tsrc provides the prediction TO this packet
  val fsrc = UInt(BSRC_SZ.W)
  val tsrc = UInt(BSRC_SZ.W)
  val ras_resp = UInt(vaddrBitsExtended.W)
  val bpd_f2_vpc = UInt(vaddrBitsExtended.W)
  val bpd_f1_vpc = UInt(vaddrBitsExtended.W)
  val bpd_f2_ghist = new GlobalHistory
  val bpd_f1_ghist = new GlobalHistory
  val bpd_f1_valid = Bool()
  val bpd_f2_valid = Bool()
}

class GlobalHistory(implicit p: Parameters) extends BoomBundle()(p)
  with HasBoomFrontendParameters
{
  // For the dual banked case, each bank ignores the contribution of the
  // last bank to the history. Thus we have to track the most recent update to the
  // history in that case
  val old_history = UInt(globalHistoryLength.W)

  val current_saw_branch_not_taken = Bool()

  val new_saw_branch_not_taken = Bool()
  val new_saw_branch_taken     = Bool()

  val ras_idx = UInt(log2Ceil(nRasEntries).W)

  def histories(bank: Int) = {
    if (nBanks == 1) {
      old_history
    } else {
      require(nBanks == 2)
      if (bank == 0) {
        old_history
      } else {
        Mux(new_saw_branch_taken                            , old_history << 1 | 1.U,
        Mux(new_saw_branch_not_taken                        , old_history << 1,
                                                              old_history))
      }
    }
  }

  def ===(other: GlobalHistory): Bool = {
    ((old_history === other.old_history) &&
     (new_saw_branch_not_taken === other.new_saw_branch_not_taken) &&
     (new_saw_branch_taken === other.new_saw_branch_taken)
    )
  }
  def =/=(other: GlobalHistory): Bool = !(this === other)

  def update(branches: UInt, cfi_taken: Bool, cfi_is_br: Bool, cfi_idx: UInt,
    cfi_valid: Bool, addr: UInt,
    cfi_is_call: Bool, cfi_is_ret: Bool): GlobalHistory = {
    val cfi_idx_fixed = cfi_idx(log2Ceil(fetchWidth)-1,0)
    val cfi_idx_oh = UIntToOH(cfi_idx_fixed)
    val new_history = Wire(new GlobalHistory)

    val not_taken_branches = branches & Mux(cfi_valid,
                                            MaskLower(cfi_idx_oh) & ~Mux(cfi_is_br && cfi_taken, cfi_idx_oh, 0.U(fetchWidth.W)),
                                            ~(0.U(fetchWidth.W)))

    if (nBanks == 1) {
      // In the single bank case every bank sees the history including the previous bank
      new_history := DontCare
      new_history.current_saw_branch_not_taken := false.B
      val saw_not_taken_branch = not_taken_branches =/= 0.U || current_saw_branch_not_taken
      new_history.old_history := Mux(cfi_is_br && cfi_taken && cfi_valid   , histories(0) << 1 | 1.U,
                                 Mux(saw_not_taken_branch                  , histories(0) << 1,
                                                                             histories(0)))
    } else {
      // In the two bank case every bank ignore the history added by the previous bank
      val base = histories(1)
      val cfi_in_bank_0 = cfi_valid && cfi_taken && cfi_idx_fixed < bankWidth.U
      val ignore_second_bank = cfi_in_bank_0 || mayNotBeDualBanked(addr)

      val first_bank_saw_not_taken = not_taken_branches(bankWidth-1,0) =/= 0.U || current_saw_branch_not_taken
      new_history.current_saw_branch_not_taken := false.B
      when (ignore_second_bank) {
        new_history.old_history := histories(1)
        new_history.new_saw_branch_not_taken := first_bank_saw_not_taken
        new_history.new_saw_branch_taken     := cfi_is_br && cfi_in_bank_0
      } .otherwise {
        new_history.old_history := Mux(cfi_is_br && cfi_in_bank_0                             , histories(1) << 1 | 1.U,
                                   Mux(first_bank_saw_not_taken                               , histories(1) << 1,
                                                                                                histories(1)))

        new_history.new_saw_branch_not_taken := not_taken_branches(fetchWidth-1,bankWidth) =/= 0.U
        new_history.new_saw_branch_taken     := cfi_valid && cfi_taken && cfi_is_br && !cfi_in_bank_0

      }
    }
    new_history.ras_idx := Mux(cfi_valid && cfi_is_call, WrapInc(ras_idx, nRasEntries),
                           Mux(cfi_valid && cfi_is_ret , WrapDec(ras_idx, nRasEntries), ras_idx))
    new_history
  }

}

/**
 * Parameters to manage a L1 Banked ICache
 */
trait HasBoomFrontendParameters extends HasL1ICacheParameters
{
  // How many banks does the ICache use?
  val nBanks = if (cacheParams.fetchBytes <= 8) 1 else 2
  // How many bytes wide is a bank?
  val bankBytes = fetchBytes/nBanks

  val bankWidth = fetchWidth/nBanks

  require(nBanks == 1 || nBanks == 2)



  // How many "chunks"/interleavings make up a cache line?
  val numChunks = cacheParams.blockBytes / bankBytes

  // Which bank is the address pointing to?
  def bank(addr: UInt) = if (nBanks == 2) addr(log2Ceil(bankBytes)) else 0.U
  def isLastBankInBlock(addr: UInt) = {
    (nBanks == 2).B && addr(blockOffBits-1, log2Ceil(bankBytes)) === (numChunks-1).U
  }
  def mayNotBeDualBanked(addr: UInt) = {
    require(nBanks == 2)
    isLastBankInBlock(addr)
  }

  def blockAlign(addr: UInt) = ~(~addr | (cacheParams.blockBytes-1).U)
  def bankAlign(addr: UInt) = ~(~addr | (bankBytes-1).U)

  def fetchIdx(addr: UInt) = addr >> log2Ceil(fetchBytes)

  def nextBank(addr: UInt) = bankAlign(addr) + bankBytes.U
  def nextFetch(addr: UInt) = {
    if (nBanks == 1) {
      bankAlign(addr) + bankBytes.U
    } else {
      require(nBanks == 2)
      bankAlign(addr) + Mux(mayNotBeDualBanked(addr), bankBytes.U, fetchBytes.U)
    }
  }

  def fetchMask(addr: UInt) = {
    val idx = addr.extract(log2Ceil(fetchWidth)+log2Ceil(coreInstBytes)-1, log2Ceil(coreInstBytes))
    if (nBanks == 1) {
      ((1 << fetchWidth)-1).U << idx
    } else {
      val shamt = idx.extract(log2Ceil(fetchWidth)-2, 0)
      val end_mask = Mux(mayNotBeDualBanked(addr), Fill(fetchWidth/2, 1.U), Fill(fetchWidth, 1.U))
      ((1 << fetchWidth)-1).U << shamt & end_mask
    }
  }

  def bankMask(addr: UInt) = {
    val idx = addr.extract(log2Ceil(fetchWidth)+log2Ceil(coreInstBytes)-1, log2Ceil(coreInstBytes))
    if (nBanks == 1) {
      1.U(1.W)
    } else {
      Mux(mayNotBeDualBanked(addr), 1.U(2.W), 3.U(2.W))
    }
  }
}



/**
 * Bundle passed into the FetchBuffer and used to combine multiple
 * relevant signals together.
 */
class FetchBundle(implicit p: Parameters) extends BoomBundle
  with HasBoomFrontendParameters
{
  val pc            = UInt(vaddrBitsExtended.W)
  val next_pc       = UInt(vaddrBitsExtended.W)
  val edge_inst     = Vec(nBanks, Bool()) // True if 1st instruction in this bundle is pc - 2
  val insts         = Vec(fetchWidth, Bits(32.W))
  val exp_insts     = Vec(fetchWidth, Bits(32.W))

  // Information for sfb folding
  // NOTE: This IS NOT equivalent to uop.pc_lob, that gets calculated in the FB
  val sfbs                 = Vec(fetchWidth, Bool())
  val sfb_masks            = Vec(fetchWidth, UInt((2*fetchWidth).W))
  val sfb_dests            = Vec(fetchWidth, UInt((1+log2Ceil(fetchBytes)).W))
  val shadowable_mask      = Vec(fetchWidth, Bool())
  val shadowed_mask        = Vec(fetchWidth, Bool())

  val cfi_idx       = Valid(UInt(log2Ceil(fetchWidth).W))
  val cfi_type      = UInt(CFI_SZ.W)
  val cfi_is_call   = Bool()
  val cfi_is_ret    = Bool()
  val cfi_npc_plus4 = Bool()

  val ras_top       = UInt(vaddrBitsExtended.W)

  val ftq_idx       = UInt(log2Ceil(ftqSz).W)
  val mask          = UInt(fetchWidth.W) // mark which words are valid instructions

  val br_mask       = UInt(fetchWidth.W)

  val ghist         = new GlobalHistory
  val lhist         = Vec(nBanks, UInt(localHistoryLength.W))

  val xcpt_pf_if    = Bool() // I-TLB miss (instruction fetch fault).
  val xcpt_ae_if    = Bool() // Access exception.

  val bp_debug_if_oh= Vec(fetchWidth, Bool())
  val bp_xcpt_if_oh = Vec(fetchWidth, Bool())

  val end_half      = Valid(UInt(16.W))


  val bpd_meta      = Vec(nBanks, UInt())

  // Source of the prediction from this bundle
  val fsrc    = UInt(BSRC_SZ.W)
  // Source of the prediction to this bundle
  val tsrc    = UInt(BSRC_SZ.W)

  val btb_hit     = Vec(fetchWidth, Bool())
  val bim_taken   = Vec(fetchWidth, Bool())
  val tage_hit    = Vec(fetchWidth, Bool())
  val tage_taken  = Vec(fetchWidth, Bool())
  val loop_hit    = Vec(fetchWidth, Bool())
  val loop_flip   = Vec(fetchWidth, Bool())
  val loop_taken  = Vec(fetchWidth, Bool())
}

/**
 * Bundle passed into the PredictTargetQueue
 */
class PredictBundle(implicit p: Parameters) extends BoomBundle
  with HasBoomFrontendParameters
{
  val pc       = UInt(vaddrBitsExtended.W)
  val ghist    = new GlobalHistory
  val mask     = UInt(fetchWidth.W)
  val fsrc     = UInt(BSRC_SZ.W)
  val tsrc     = UInt(BSRC_SZ.W)
  val f3       = new BranchPredictionBundle
  val ras_resp = UInt(vaddrBitsExtended.W)
  val f1_vpc   = UInt(vaddrBitsExtended.W)
  val f2_vpc   = UInt(vaddrBitsExtended.W)
  val f1_ghist = new GlobalHistory
  val f2_ghist = new GlobalHistory
  val f1_valid = Bool()
  val f2_valid = Bool()
}


/**
 * IO for the BOOM Frontend to/from the CPU
 */
class BoomFrontendIO(implicit p: Parameters) extends BoomBundle
{
  // Give the backend a packet of instructions.
  val fetchpacket       = Flipped(new DecoupledIO(new FetchBufferResp))

  // 1 for xcpt/jalr/auipc/flush
  val get_pc            = Flipped(Vec(2, new GetPCFromFtqIO()))
  val debug_ftq_idx     = Output(Vec(coreWidth, UInt(log2Ceil(ftqSz).W)))
  val debug_fetch_pc    = Input(Vec(coreWidth, UInt(vaddrBitsExtended.W)))

  // Breakpoint info
  val status            = Output(new MStatus)
  val bp                = Output(Vec(nBreakpoints, new BP))
  val mcontext          = Output(UInt(coreParams.mcontextWidth.W))
  val scontext          = Output(UInt(coreParams.scontextWidth.W))

  val sfence = Valid(new SFenceReq)

  val brupdate          = Output(new BrUpdateInfo)

  // Redirects change the PC
  val redirect_flush   = Output(Bool()) // Flush and hang the frontend?
  val redirect_val     = Output(Bool()) // Redirect the frontend?
  val redirect_pc      = Output(UInt()) // Where do we redirect to?
  val redirect_ftq_idx = Output(UInt()) // Which ftq entry should we reset to?
  val redirect_ghist   = Output(new GlobalHistory) // What are we setting as the global history?

  val commit = Valid(UInt(ftqSz.W))

  val flush_icache = Output(Bool())

  val perf = Input(new FrontendPerfEvents)
}

/**
 * Top level Frontend class
 *
 * @param icacheParams parameters for the icache
 * @param hartid id for the hardware thread of the core
 */
class BoomFrontend(val icacheParams: ICacheParams, staticIdForMetadataUseOnly: Int)(implicit p: Parameters) extends LazyModule
{
  lazy val module = new BoomFrontendModule(this)
  val icache = LazyModule(new boom.ifu.ICache(icacheParams, staticIdForMetadataUseOnly))
  val masterNode = icache.masterNode
  val resetVectorSinkNode = BundleBridgeSink[UInt](Some(() =>
    UInt(masterNode.edges.out.head.bundle.addressBits.W)))
}

/**
 * Bundle wrapping the IO for the Frontend as a whole
 *
 * @param outer top level Frontend class
 */
class BoomFrontendBundle(val outer: BoomFrontend) extends CoreBundle()(outer.p)
{
  val cpu = Flipped(new BoomFrontendIO())
  val ptw = new TLBPTWIO()
  val errors = new ICacheErrors
}

/**
 * Main Frontend module that connects the icache, TLB, fetch controller,
 * and branch prediction pipeline together.
 *
 * @param outer top level Frontend class
 */
class BoomFrontendModule(outer: BoomFrontend) extends LazyModuleImp(outer)
  with HasBoomCoreParameters
  with HasBoomFrontendParameters
{

  // add a cycle counter
  val debug_cycles = freechips.rocketchip.util.WideCounter(32)

  val io = IO(new BoomFrontendBundle(outer))
  val io_reset_vector = outer.resetVectorSinkNode.bundle
  implicit val edge = outer.masterNode.edges.out(0)
  require(fetchWidth*coreInstBytes == outer.icacheParams.fetchBytes)

  val bpd = Module(new BranchPredictor)
  bpd.io.f3_fire := false.B
  val ras = Module(new BoomRAS)

  val icache = outer.icache.module
  icache.io.invalidate := io.cpu.flush_icache
  val tlb = Module(new TLB(true, log2Ceil(fetchBytes), TLBConfig(nTLBSets, nTLBWays)))
  io.ptw <> tlb.io.ptw
  io.cpu.perf.tlbMiss := io.ptw.req.fire
  io.cpu.perf.acquire := icache.io.perf.acquire

  // --------------------------------------------------------
  // **** NextPC Select (F0) ****
  //      Send request to Branch Predictor
  // --------------------------------------------------------

  val s0_vpc       = WireInit(0.U(vaddrBitsExtended.W))
  val s0_ghist     = WireInit((0.U).asTypeOf(new GlobalHistory))
  val s0_tsrc      = WireInit(0.U(BSRC_SZ.W))
  val s0_valid     = WireInit(false.B)


  when (RegNext(reset.asBool) && !reset.asBool) {
    s0_valid   := true.B
    s0_vpc     := io_reset_vector
    s0_ghist   := (0.U).asTypeOf(new GlobalHistory)
    s0_tsrc    := BSRC_C
  }


  bpd.io.f0_req.valid      := s0_valid
  bpd.io.f0_req.bits.pc    := s0_vpc
  bpd.io.f0_req.bits.ghist := s0_ghist

  // printf("Cycle %d vpc %x\n", debug_cycles.value, s0_vpc)

  // --------------------------------------------------------
  // **** uBTB (F1) ****
  //      Redirect by f1 bpd resp
  // --------------------------------------------------------
  val s1_vpc       = RegNext(s0_vpc)
  val s1_valid     = RegNext(s0_valid, false.B)
  val s1_ghist     = RegNext(s0_ghist)
  val f1_clear     = WireInit(false.B)
  val s1_tsrc      = RegNext(s0_tsrc)
  

  val s1_bpd_resp = bpd.io.resp.f1


  val f1_mask = fetchMask(s1_vpc)
  val f1_redirects = (0 until fetchWidth) map { i =>
    s1_valid && f1_mask(i) && s1_bpd_resp.preds(i).predicted_pc.valid &&
    (s1_bpd_resp.preds(i).is_jal ||
      (s1_bpd_resp.preds(i).is_br && s1_bpd_resp.preds(i).taken))
  }
  val f1_redirect_idx = PriorityEncoder(f1_redirects)
  val f1_do_redirect = f1_redirects.reduce(_||_) && useBPD.B
  val f1_targs = s1_bpd_resp.preds.map(_.predicted_pc.bits)
  val f1_predicted_target = Mux(f1_do_redirect,
                                f1_targs(f1_redirect_idx),
                                nextFetch(s1_vpc))

  val f1_predicted_ghist = s1_ghist.update(
    s1_bpd_resp.preds.map(p => p.is_br && p.predicted_pc.valid).asUInt & f1_mask,
    s1_bpd_resp.preds(f1_redirect_idx).taken && f1_do_redirect,
    s1_bpd_resp.preds(f1_redirect_idx).is_br,
    f1_redirect_idx,
    f1_do_redirect,
    s1_vpc,
    false.B,
    false.B)

  when (s1_valid) {
    // Stop fetching on fault
    s0_valid     := true.B
    s0_tsrc      := BSRC_1
    s0_vpc       := f1_predicted_target
    s0_ghist     := f1_predicted_ghist
  }

  // --------------------------------------------------------
  // **** BTB && Bim (F1) ****
  //      Redirect by f2 bpd resp
  // --------------------------------------------------------

  val s2_valid = RegNext(s1_valid && !f1_clear, false.B)
  val s2_vpc   = RegNext(s1_vpc)
  val s2_ghist = Reg(new GlobalHistory)
  s2_ghist := s1_ghist
  val s2_tsrc = RegNext(s1_tsrc) // tsrc provides the predictor component which provided the prediction TO this instruction
  val s2_fsrc = WireInit(BSRC_1) // fsrc provides the predictor component which provided the prediction FROM this instruction
  val f2_clear = WireInit(false.B)
  val f3_ready = Wire(Bool())


  val f2_bpd_resp = bpd.io.resp.f2
  val f2_mask = fetchMask(s2_vpc)
  val f2_redirects = (0 until fetchWidth) map { i =>
    s2_valid && f2_mask(i) && f2_bpd_resp.preds(i).predicted_pc.valid &&
    (f2_bpd_resp.preds(i).is_jal ||
      (f2_bpd_resp.preds(i).is_br && f2_bpd_resp.preds(i).taken))
  }
  val f2_redirect_idx = PriorityEncoder(f2_redirects)
  val f2_targs = f2_bpd_resp.preds.map(_.predicted_pc.bits)
  val f2_do_redirect = f2_redirects.reduce(_||_) && useBPD.B
  val f2_predicted_target = Mux(f2_do_redirect,
                                f2_targs(f2_redirect_idx),
                                nextFetch(s2_vpc))
  val f2_predicted_ghist = s2_ghist.update(
    f2_bpd_resp.preds.map(p => p.is_br && p.predicted_pc.valid).asUInt & f2_mask,
    f2_bpd_resp.preds(f2_redirect_idx).taken && f2_do_redirect,
    f2_bpd_resp.preds(f2_redirect_idx).is_br,
    f2_redirect_idx,
    f2_do_redirect,
    s2_vpc,
    false.B,
    false.B)

  val f2_correct_f1_ghist = s1_ghist =/= f2_predicted_ghist && enableGHistStallRepair.B

  when (s2_valid) {
    when (s1_valid && s1_vpc === f2_predicted_target && !f2_correct_f1_ghist) {
      // We trust our prediction of what the global history for the next branch should be
      s2_ghist := f2_predicted_ghist
    }
    when ((s1_valid && (s1_vpc =/= f2_predicted_target || f2_correct_f1_ghist)) || !s1_valid) {
      f1_clear := true.B

      s0_valid     := true.B
      s0_vpc       := f2_predicted_target
      s0_ghist     := f2_predicted_ghist
      s2_fsrc      := BSRC_2
      s0_tsrc      := BSRC_2
    }
  }

  val ras_read_idx = RegInit(0.U(log2Ceil(nRasEntries)))
  ras.io.read_idx := ras_read_idx
  when (s2_valid && !f2_clear) {
    ras_read_idx := s2_ghist.ras_idx
    ras.io.read_idx := s2_ghist.ras_idx
  }

  // --------------------------------------------------------
  // **** F3 ****
  //    pc && f3_bpd_resp enter the ptq
  // --------------------------------------------------------
  val f3_clear = WireInit(false.B)

  val ptq = Module(new PredictTargetQueue)
  ptq.io.clear := reset.asBool || f3_clear
  

  val deq_ready = WireInit(false.B)
  val read_ready = WireInit(true.B)

  val s3_valid = RegNext(s2_valid && !f2_clear, false.B)
  val s3_vpc   = RegNext(s2_vpc)
  val s3_ghist = RegNext(s2_ghist)
  val s3_fsrc  = RegNext(s2_fsrc)
  val s3_tsrc  = RegNext(s2_tsrc)

  val f3_bpd_resp = bpd.io.resp.f3
  val f3_mask = fetchMask(s3_vpc)
  val f3_redirects = (0 until fetchWidth) map { i =>
    s3_valid && f3_mask(i) && f3_bpd_resp.preds(i).predicted_pc.valid &&
    (f3_bpd_resp.preds(i).is_jal || 
     (f3_bpd_resp.preds(i).is_br && f3_bpd_resp.preds(i).taken))
  }
  val f3_redirect_idx = PriorityEncoder(f3_redirects)
  val f3_targs = f3_bpd_resp.preds.map(_.predicted_pc.bits)
  val f3_do_redirect = f3_redirects.reduce(_||_) && useBPD.B
  val f3_predicted_target = Mux(f3_do_redirect,
                                f3_targs(f3_redirect_idx),
                                nextFetch(s3_vpc))
  val f3_predicted_ghist = s3_ghist.update(
    f3_bpd_resp.preds.map(p => p.is_br && p.predicted_pc.valid).asUInt & f3_mask,
    f3_bpd_resp.preds(f3_redirect_idx).taken && f3_do_redirect,
    f3_bpd_resp.preds(f3_redirect_idx).is_br,
    f3_redirect_idx,
    f3_do_redirect,
    s3_vpc,
    false.B,
    false.B
  )

  val f3_correct_f1_ghist = s1_ghist =/= f3_predicted_ghist && enableGHistStallRepair.B
  val f3_correct_f2_ghist = s2_ghist =/= f3_predicted_ghist && enableGHistStallRepair.B

  when (s3_valid && !f3_ready) {
    s0_valid := true.B
    s0_vpc   := s3_vpc
    s0_ghist := s3_ghist
    s0_tsrc  := s3_tsrc
    f1_clear := true.B
    f2_clear := true.B
  } .elsewhen (s3_valid && f3_ready) {
    when (s2_valid && s2_vpc === f3_predicted_target && !f3_correct_f2_ghist) {
      s3_ghist := f3_predicted_ghist
    } .elsewhen (!s2_valid && s1_valid && s1_vpc === f3_predicted_target && !f3_correct_f1_ghist) {
      s2_ghist := f3_predicted_ghist
    } .elsewhen ((s2_valid && (s2_vpc =/= f3_predicted_target || f3_correct_f2_ghist)) ||
                 (!s2_valid && s1_valid && (s1_vpc =/= f3_predicted_target || f3_correct_f1_ghist)) ||
                 (!s2_valid && !s1_valid)) {            
      f2_clear := true.B
      f1_clear := true.B

      s0_valid := true.B
      s0_vpc   := f3_predicted_target
      s0_ghist := f3_predicted_ghist
      s0_tsrc  := BSRC_3
      s3_fsrc  := BSRC_3
    }
  }
  
  
  f3_ready := ptq.io.enq.ready

  ptq.io.enq.valid          := s3_valid
  ptq.io.enq.bits.pc        := s3_vpc
  ptq.io.enq.bits.ghist     := s3_ghist
  ptq.io.enq.bits.mask      := fetchMask(s3_vpc)
  ptq.io.enq.bits.fsrc      := s3_fsrc
  ptq.io.enq.bits.tsrc      := s3_tsrc
  ptq.io.enq.bits.f3        := bpd.io.resp.f3
  ptq.io.enq.bits.ras_resp  := ras.io.read_addr

  ptq.io.enq.bits.f2_vpc    := s2_vpc
  ptq.io.enq.bits.f1_vpc    := s1_vpc
  ptq.io.enq.bits.f2_ghist  := s2_ghist
  ptq.io.enq.bits.f1_ghist  := s1_ghist
  ptq.io.enq.bits.f2_valid  := s2_valid
  ptq.io.enq.bits.f1_valid  := s1_valid

  /*
  when (ptq.io.enq.fire) {
    printf("Cycle %d enter ptq %x\n", debug_cycles.value, ptq.io.enq.bits.pc)
  }
  */
  


  when (ptq.io.enq.fire) {
    bpd.io.f3_fire := true.B
  }

  ptq.io.deq.ready := deq_ready
  ptq.io.read.ready := read_ready
  ptq.io.reset := false.B

  // --------------------------------------------------------
  // **** F4 ****
  //    pc && f3_bpd_resp leave the ptq
  //    send Request to ICache
  // --------------------------------------------------------

  val f4_vpc          = WireInit(0.U(vaddrBitsExtended.W))
  val f4_ghist        = WireInit((0.U).asTypeOf(new GlobalHistory))
  val f4_tsrc         = WireInit(0.U(BSRC_SZ.W))
  val f4_fsrc         = WireInit(0.U(BSRC_SZ.W))
  val f4_valid        = WireInit(false.B)
  val f4_is_replay    = WireInit(false.B)
  val f4_is_sfence    = WireInit(false.B)
  val f4_replay_resp  = Wire(new TLBResp)
  val f4_replay_ppc   = Wire(UInt())
  val f4_bpd_resp     = WireInit((0.U).asTypeOf(new BranchPredictionBundle))
  val f4_ras_resp     = WireInit(0.U(vaddrBitsExtended.W))

  val f4_bpd_f1_vpc      = WireInit(0.U(vaddrBitsExtended.W))
  val f4_bpd_f2_vpc      = WireInit(0.U(vaddrBitsExtended.W))
  val f4_bpd_f1_ghist    = WireInit((0.U).asTypeOf(new GlobalHistory))
  val f4_bpd_f2_ghist    = WireInit((0.U).asTypeOf(new GlobalHistory))
  val f4_bpd_f1_valid    = WireInit(false.B)
  val f4_bpd_f2_valid    = WireInit(false.B)

  
  when (ptq.io.read.valid && read_ready) {
    f4_valid     := true.B
    f4_vpc       := ptq.io.read.bits.pc
    f4_ghist     := ptq.io.read.bits.ghist
    f4_fsrc      := ptq.io.read.bits.fsrc
    f4_tsrc      := ptq.io.read.bits.tsrc
    f4_bpd_resp  := ptq.io.read.bits.f3
    f4_ras_resp  := ptq.io.read.bits.ras_resp

    f4_bpd_f1_vpc := ptq.io.read.bits.f1_vpc
    f4_bpd_f2_vpc := ptq.io.read.bits.f2_vpc
    f4_bpd_f1_ghist := ptq.io.read.bits.f1_ghist
    f4_bpd_f2_ghist := ptq.io.read.bits.f2_ghist
    f4_bpd_f1_valid := ptq.io.read.bits.f1_valid
    f4_bpd_f2_valid := ptq.io.read.bits.f2_valid

    // printf("Cycle %d read from ptq %x with f4_vpc %x\n", debug_cycles.value, ptq.io.read.bits.pc, f4_vpc)
  } .otherwise {
    f4_valid     := false.B
  }
  
  /*
  when (f4_valid) {
    printf("Cycle %d f4 vpc: %x\n", debug_cycles.value, f4_vpc)
  }
  */
  
  // printf("f4 vpc: %x\n", f4_vpc)

  icache.io.req.valid     := f4_valid
  icache.io.req.bits.addr := f4_vpc
  
  /*
  when (icache.io.req.valid) {
    printf("Cycle %d icache request pc: %x\n", debug_cycles.value, icache.io.req.bits.addr)
  }
  */
  

  // --------------------------------------------------------
  // **** F5 ****
  //    Translate VPC
  // --------------------------------------------------------
  val f5_vpc        = RegNext(f4_vpc)
  val f5_ghist      = RegNext(f4_ghist)
  val f5_fsrc       = RegNext(f4_fsrc)
  val f5_tsrc       = RegNext(f4_tsrc)
  val f5_valid      = RegNext(f4_valid, false.B)
  val f5_is_replay  = RegNext(f4_is_replay)
  val f5_is_sfence  = RegNext(f4_is_sfence)
  val f5_clear      = WireInit(false.B)
  val f5_bpd_resp   = RegNext(f4_bpd_resp)
  val f5_ras_resp   = RegNext(f4_ras_resp)

  val f5_bpd_f1_vpc = RegNext(f4_bpd_f1_vpc)
  val f5_bpd_f2_vpc = RegNext(f4_bpd_f2_vpc)
  val f5_bpd_f1_ghist = RegNext(f4_bpd_f1_ghist)
  val f5_bpd_f2_ghist = RegNext(f4_bpd_f2_ghist)
  val f5_bpd_f1_valid = RegNext(f4_bpd_f1_valid)
  val f5_bpd_f2_valid = RegNext(f4_bpd_f2_valid)

  tlb.io.req.valid            := (f5_valid && !f5_is_replay && !f5_clear) || f5_is_sfence
  tlb.io.req.bits.cmd         := DontCare
  tlb.io.req.bits.vaddr       := f5_vpc
  tlb.io.req.bits.passthrough := false.B
  tlb.io.req.bits.size        := log2Ceil(coreInstBytes * fetchWidth).U
  tlb.io.sfence               := RegNext(io.cpu.sfence)
  tlb.io.kill                 := false.B

  val f5_tlb_miss = !f5_is_replay && tlb.io.resp.miss
  val f5_tlb_resp = Mux(f5_is_replay, RegNext(f4_replay_resp), tlb.io.resp)
  val f5_ppc      = Mux(f5_is_replay, RegNext(f4_replay_ppc), tlb.io.resp.paddr)

  icache.io.s1_paddr := f5_ppc
  icache.io.s1_kill  := tlb.io.resp.miss || f5_clear

  when (f5_valid && !f5_tlb_miss) {
    when (f5_tlb_resp.ae.inst || f5_tlb_resp.pf.inst) {
      f4_valid := false.B
    }
    f4_is_replay := false.B
    read_ready   := !(f5_tlb_resp.ae.inst || f5_tlb_resp.pf.inst)
    // printf("Cycle %d !f5_tlb_miss %x read_ready: %d\n", debug_cycles.value, f5_vpc, read_ready)
    // printf("Cycle %d vpc %x, ae %d, pf %d\n", debug_cycles.value, f5_vpc, f5_tlb_resp.ae.inst, f5_tlb_resp.pf.inst)
  }

  /*
  when (f5_valid) {
    printf("Cycle %d f5 vpc: %x\n", debug_cycles.value, f5_vpc)
  }
  */
  
  


  val f6_valid = RegNext(f5_valid && !f5_clear, false.B)
  val f6_vpc   = RegNext(f5_vpc)
  val f6_ghist = RegNext(f5_ghist)
  val f6_fsrc  = RegNext(f5_fsrc)
  val f6_tsrc  = RegNext(f5_tsrc)
  val f6_ppc   = RegNext(f5_ppc)
  val f6_bpd_resp = RegNext(f5_bpd_resp)
  val f6_ras_resp = RegNext(f5_ras_resp)
  val f6_clear = WireInit(false.B)
  val f6_tlb_resp = RegNext(f5_tlb_resp)
  val f6_tlb_miss = RegNext(f5_tlb_miss)
  val f6_is_replay = RegNext(f5_is_replay) && f6_valid
  val f6_xcpt  = f6_valid && (f6_tlb_resp.ae.inst || f6_tlb_resp.pf.inst) && !f6_is_replay
  
  val f6_bpd_f1_vpc = RegNext(f5_bpd_f1_vpc)
  val f6_bpd_f2_vpc = RegNext(f5_bpd_f2_vpc)
  val f6_bpd_f1_ghist = RegNext(f5_bpd_f1_ghist)
  val f6_bpd_f2_ghist = RegNext(f5_bpd_f2_ghist)
  val f6_bpd_f1_valid = RegNext(f5_bpd_f1_valid)
  val f6_bpd_f2_valid = RegNext(f5_bpd_f2_valid)
  
  val f7_ready = Wire(Bool())

  icache.io.s2_kill := f6_xcpt

  when ((f6_valid && !icache.io.resp.valid) ||
        (f6_valid && icache.io.resp.valid && !f7_ready)) {
    f4_valid     := (!f6_tlb_resp.ae.inst && !f6_tlb_resp.pf.inst) || f6_is_replay || f6_tlb_miss
    f4_vpc       := f6_vpc
    f4_bpd_resp  := f6_bpd_resp
    f4_is_replay := f6_valid && icache.io.resp.valid
    f4_ghist     := f6_ghist
    f4_tsrc      := f6_tsrc
    f4_ras_resp  := f6_ras_resp

    f4_bpd_f1_vpc := f6_bpd_f1_vpc
    f4_bpd_f2_vpc := f6_bpd_f2_vpc
    f4_bpd_f1_ghist := f6_bpd_f1_ghist
    f4_bpd_f2_ghist := f6_bpd_f2_ghist
    f4_bpd_f1_valid := f6_bpd_f1_valid
    f4_bpd_f2_valid := f6_bpd_f2_valid

    f5_clear     := true.B
    ptq.io.reset := true.B
    // printf("Cycle %d redo icache access %x with f4_vpc %x valid: %d icache_valid: %d f7_ready: %d\n", debug_cycles.value, f6_vpc, f4_vpc, f6_valid, icache.io.resp.valid, f7_ready)
  } .elsewhen(f6_valid && f7_ready) {
    when (!f5_valid) {
      f5_clear := true.B
      when ((f6_tlb_resp.ae.inst || f6_tlb_resp.pf.inst) && !f6_is_replay) {
        f4_valid := false.B
      }
      // f4_valid     := !((f6_tlb_resp.ae.inst || f6_tlb_resp.pf.inst) && !f6_is_replay)
      read_ready := !((f6_tlb_resp.ae.inst || f6_tlb_resp.pf.inst) && !f6_is_replay)
      f4_is_replay := false.B

      /*
      when (f4_ready) { 
        printf("f6 f4_ready: true %x\n", f6_vpc)
      }
      */
      // printf("Cycle %d f5_valid false f4_valid: %d, tlb %d, replay %d\n", debug_cycles.value, f4_valid, (f6_tlb_resp.ae.inst || f6_tlb_resp.pf.inst), f6_is_replay)
    }
    when (icache.io.resp.valid) {
      f4_is_replay    := false.B
      deq_ready       := true.B
      // printf("Cycle %d icache access success\n", debug_cycles.value)
    }
    ptq.io.reset := false.B
  }. otherwise {
    ptq.io.reset := false.B
  }
  f4_replay_resp := f6_tlb_resp
  f4_replay_ppc  := f6_ppc
  /*
  when (f6_valid && !f6_tlb_miss) {
    printf("Cycle %d vpc %x, ae %d, pf %d\n", debug_cycles.value, f6_vpc, f6_tlb_resp.ae.inst, f6_tlb_resp.pf.inst)
  }
  */
  /*
  when (f6_valid) {
    printf("f6 vpc: %x", f6_vpc)
    when (icache.io.resp.valid) {
      printf("icache resp success\n")
    }
  }
  */
  // printf("ptq deq fire %x\n", ptq.io.deq.fire)
  // printf("Cycle %d f6_vpc %x with valid %d\n", debug_cycles.value, f6_vpc, f6_valid)

  val f7_clear = WireInit(false.B)
  val f7 = withReset(reset.asBool || f7_clear) {
    Module(new Queue(new FrontendResp, 1, pipe=true, flow=false)) }

  // Queue up the bpd resp as well, incase f7 backpressures f6
  // This is "flow" because the response (enq) arrives in f6, not f5
  val f7_bpd_resp = withReset(reset.asBool || f7_clear) {
    Module(new Queue(new BranchPredictionBundle, 1, pipe=true, flow=false)) }


  val f8_ready = Wire(Bool())
  f7_ready := f7.io.enq.ready
  f7.io.enq.valid   := (f6_valid && !f6_clear &&
    (icache.io.resp.valid || ((f6_tlb_resp.ae.inst || f6_tlb_resp.pf.inst) && !f6_tlb_miss))
  )
  f7.io.enq.bits.pc := f6_vpc
  f7.io.enq.bits.data  := Mux(f6_xcpt, 0.U, icache.io.resp.bits.data)
  f7.io.enq.bits.ghist := f6_ghist
  f7.io.enq.bits.mask := fetchMask(f6_vpc)
  f7.io.enq.bits.xcpt := f6_tlb_resp
  f7.io.enq.bits.fsrc := f6_fsrc
  f7.io.enq.bits.tsrc := f6_tsrc
  f7.io.enq.bits.ras_resp := f6_ras_resp

  f7.io.enq.bits.bpd_f1_vpc := f6_bpd_f1_vpc
  f7.io.enq.bits.bpd_f2_vpc := f6_bpd_f2_vpc
  f7.io.enq.bits.bpd_f1_ghist := f6_bpd_f1_ghist
  f7.io.enq.bits.bpd_f2_ghist := f6_bpd_f2_ghist
  f7.io.enq.bits.bpd_f1_valid := f6_bpd_f1_valid
  f7.io.enq.bits.bpd_f2_valid := f6_bpd_f2_valid
  
  /*
  when (f7.io.enq.valid) {
    printf("Cycle %d f7 enq %x %x\n", debug_cycles.value, f7.io.enq.bits.pc, f7.io.enq.bits.data)
  }
  */


  // The BPD resp comes in f3
  f7_bpd_resp.io.enq.valid := f7.io.enq.valid
  f7_bpd_resp.io.enq.bits  := f6_bpd_resp

  f7.io.deq.ready := f8_ready
  f7_bpd_resp.io.deq.ready := f8_ready


  val f7_imemresp     = f7.io.deq.bits
  val f7_bank_mask    = bankMask(f7_imemresp.pc)
  val f7_data         = f7_imemresp.data
  val f7_aligned_pc   = bankAlign(f7_imemresp.pc)
  val f7_is_last_bank_in_block = isLastBankInBlock(f7_aligned_pc)
  val f7_is_rvc       = Wire(Vec(fetchWidth, Bool()))
  val f7_redirects    = Wire(Vec(fetchWidth, Bool()))
  val f7_targs        = Wire(Vec(fetchWidth, UInt(vaddrBitsExtended.W)))
  val f7_cfi_types    = Wire(Vec(fetchWidth, UInt(CFI_SZ.W)))
  val f7_shadowed_mask = Wire(Vec(fetchWidth, Bool()))
  val f7_fetch_bundle = Wire(new FetchBundle)
  val f7_mask         = Wire(Vec(fetchWidth, Bool()))
  val f7_br_mask      = Wire(Vec(fetchWidth, Bool()))
  val f7_call_mask    = Wire(Vec(fetchWidth, Bool()))
  val f7_ret_mask     = Wire(Vec(fetchWidth, Bool()))
  val f7_npc_plus4_mask = Wire(Vec(fetchWidth, Bool()))
  val f7_btb_mispredicts = Wire(Vec(fetchWidth, Bool()))
  f7_fetch_bundle.mask := f7_mask.asUInt
  f7_fetch_bundle.br_mask := f7_br_mask.asUInt
  f7_fetch_bundle.pc := f7_imemresp.pc
  f7_fetch_bundle.ftq_idx := 0.U // This gets assigned later
  f7_fetch_bundle.xcpt_pf_if := f7_imemresp.xcpt.pf.inst
  f7_fetch_bundle.xcpt_ae_if := f7_imemresp.xcpt.ae.inst
  f7_fetch_bundle.fsrc := f7_imemresp.fsrc
  f7_fetch_bundle.tsrc := f7_imemresp.tsrc
  f7_fetch_bundle.shadowed_mask := f7_shadowed_mask

  // Save bpd resps into fetch bundle
  val f7_preds = f7_bpd_resp.io.deq.bits.preds
  f7_fetch_bundle.btb_hit     := f7_preds.map(_.btb_hit)
  f7_fetch_bundle.bim_taken   := f7_preds.map(_.bim_taken)
  f7_fetch_bundle.tage_hit    := f7_preds.map(_.tage_hit)
  f7_fetch_bundle.tage_taken  := f7_preds.map(_.tage_taken)
  f7_fetch_bundle.loop_hit    := f7_preds.map(_.loop_hit)
  f7_fetch_bundle.loop_flip   := f7_preds.map(_.loop_flip)
  f7_fetch_bundle.loop_taken  := f7_preds.map(_.loop_taken)

  // Tracks trailing 16b of previous fetch packet
  val f7_prev_half    = Reg(UInt(16.W))
  // Tracks if last fetchpacket contained a half-inst
  val f7_prev_is_half = RegInit(false.B)

  require(fetchWidth >= 4) // Logic gets kind of annoying with fetchWidth = 2
  def isRVC(inst: UInt) = (inst(1,0) =/= 3.U)
  var redirect_found = false.B
  var bank_prev_is_half = f7_prev_is_half
  var bank_prev_half    = f7_prev_half
  var last_inst = 0.U(16.W)
  for (b <- 0 until nBanks) {
    val bank_data  = f7_data((b+1)*bankWidth*16-1, b*bankWidth*16)
    val bank_mask  = Wire(Vec(bankWidth, Bool()))
    val bank_insts = Wire(Vec(bankWidth, UInt(32.W)))

    for (w <- 0 until bankWidth) {
      val i = (b * bankWidth) + w

      val valid = Wire(Bool())
      val bpu = Module(new BreakpointUnit(nBreakpoints))
      bpu.io.status   := io.cpu.status
      bpu.io.bp       := io.cpu.bp
      bpu.io.ea       := DontCare
      bpu.io.mcontext := io.cpu.mcontext
      bpu.io.scontext := io.cpu.scontext

      val brsigs = Wire(new BranchDecodeSignals)
      if (w == 0) {
        val inst0 = Cat(bank_data(15,0), f7_prev_half)
        val inst1 = bank_data(31,0)
        val exp_inst0 = ExpandRVC(inst0)
        val exp_inst1 = ExpandRVC(inst1)
        val pc0 = (f7_aligned_pc + (i << log2Ceil(coreInstBytes)).U - 2.U)
        val pc1 = (f7_aligned_pc + (i << log2Ceil(coreInstBytes)).U)

        val bpd_decoder0 = Module(new BranchDecode)
        bpd_decoder0.io.inst := exp_inst0
        bpd_decoder0.io.pc   := pc0
        val bpd_decoder1 = Module(new BranchDecode)
        bpd_decoder1.io.inst := exp_inst1
        bpd_decoder1.io.pc   := pc1

        when (bank_prev_is_half) {
          bank_insts(w)                := inst0
          f7_fetch_bundle.insts(i)     := inst0
          f7_fetch_bundle.exp_insts(i) := exp_inst0
          bpu.io.pc                    := pc0
          brsigs                       := bpd_decoder0.io.out
          f7_fetch_bundle.edge_inst(b) := true.B
          if (b > 0) {
            val inst0b     = Cat(bank_data(15,0), last_inst)
            val exp_inst0b = ExpandRVC(inst0b)
            val bpd_decoder0b = Module(new BranchDecode)
            bpd_decoder0b.io.inst := exp_inst0b
            bpd_decoder0b.io.pc   := pc0

            when (f7_bank_mask(b-1)) {
              bank_insts(w)                := inst0b
              f7_fetch_bundle.insts(i)     := inst0b
              f7_fetch_bundle.exp_insts(i) := exp_inst0b
              brsigs                       := bpd_decoder0b.io.out
            }
          }
        } .otherwise {
          bank_insts(w)                := inst1
          f7_fetch_bundle.insts(i)     := inst1
          f7_fetch_bundle.exp_insts(i) := exp_inst1
          bpu.io.pc                    := pc1
          brsigs                       := bpd_decoder1.io.out
          f7_fetch_bundle.edge_inst(b) := false.B
        }
        valid := true.B
      } else {
        val inst = Wire(UInt(32.W))
        val exp_inst = ExpandRVC(inst)
        val pc = f7_aligned_pc + (i << log2Ceil(coreInstBytes)).U
        val bpd_decoder = Module(new BranchDecode)
        bpd_decoder.io.inst := exp_inst
        bpd_decoder.io.pc   := pc

        bank_insts(w)                := inst
        f7_fetch_bundle.insts(i)     := inst
        f7_fetch_bundle.exp_insts(i) := exp_inst
        bpu.io.pc                    := pc
        brsigs                       := bpd_decoder.io.out
        if (w == 1) {
          // Need special case since 0th instruction may carry over the wrap around
          inst  := bank_data(47,16)
          valid := bank_prev_is_half || !(bank_mask(0) && !isRVC(bank_insts(0)))
        } else if (w == bankWidth - 1) {
          inst  := Cat(0.U(16.W), bank_data(bankWidth*16-1,(bankWidth-1)*16))
          valid := !((bank_mask(w-1) && !isRVC(bank_insts(w-1))) ||
            !isRVC(inst))
        } else {
          inst  := bank_data(w*16+32-1,w*16)
          valid := !(bank_mask(w-1) && !isRVC(bank_insts(w-1)))
        }
      }

      f7_is_rvc(i) := isRVC(bank_insts(w))


      bank_mask(w) := f7.io.deq.valid && f7_imemresp.mask(i) && valid && !redirect_found
      f7_mask  (i) := f7.io.deq.valid && f7_imemresp.mask(i) && valid && !redirect_found
      f7_targs (i) := Mux(brsigs.cfi_type === CFI_JALR,
        f7_bpd_resp.io.deq.bits.preds(i).predicted_pc.bits,
        brsigs.target)

      // Flush BTB entries for JALs if we mispredict the target
      f7_btb_mispredicts(i) := (brsigs.cfi_type === CFI_JAL && valid &&
        f7_bpd_resp.io.deq.bits.preds(i).predicted_pc.valid &&
        (f7_bpd_resp.io.deq.bits.preds(i).predicted_pc.bits =/= brsigs.target)
      )


      f7_npc_plus4_mask(i) := (if (w == 0) {
        !f7_is_rvc(i) && !bank_prev_is_half
      } else {
        !f7_is_rvc(i)
      })
      val offset_from_aligned_pc = (
        (i << 1).U((log2Ceil(icBlockBytes)+1).W) +
        brsigs.sfb_offset.bits -
        Mux(bank_prev_is_half && (w == 0).B, 2.U, 0.U)
      )
      val lower_mask = Wire(UInt((2*fetchWidth).W))
      val upper_mask = Wire(UInt((2*fetchWidth).W))
      lower_mask := UIntToOH(i.U)
      upper_mask := UIntToOH(offset_from_aligned_pc(log2Ceil(fetchBytes)+1,1)) << Mux(f7_is_last_bank_in_block, bankWidth.U, 0.U)

      f7_fetch_bundle.sfbs(i) := (
        f7_mask(i) &&
        brsigs.sfb_offset.valid &&
        (offset_from_aligned_pc <= Mux(f7_is_last_bank_in_block, (fetchBytes+bankBytes).U,(2*fetchBytes).U))
      )
      f7_fetch_bundle.sfb_masks(i)       := ~MaskLower(lower_mask) & ~MaskUpper(upper_mask)
      f7_fetch_bundle.shadowable_mask(i) := (!(f7_fetch_bundle.xcpt_pf_if || f7_fetch_bundle.xcpt_ae_if || bpu.io.debug_if || bpu.io.xcpt_if) &&
                                             f7_bank_mask(b) &&
                                             (brsigs.shadowable || !f7_mask(i)))
      f7_fetch_bundle.sfb_dests(i)       := offset_from_aligned_pc

      // Redirect if
      //  1) its a JAL/JALR (unconditional)
      //  2) the BPD believes this is a branch and says we should take it
      f7_redirects(i)    := f7_mask(i) && (
        brsigs.cfi_type === CFI_JAL || brsigs.cfi_type === CFI_JALR ||
        (brsigs.cfi_type === CFI_BR && f7_bpd_resp.io.deq.bits.preds(i).taken && useBPD.B)
      )

      f7_br_mask(i)   := f7_mask(i) && brsigs.cfi_type === CFI_BR
      f7_cfi_types(i) := brsigs.cfi_type
      f7_call_mask(i) := brsigs.is_call
      f7_ret_mask(i)  := brsigs.is_ret

      f7_fetch_bundle.bp_debug_if_oh(i) := bpu.io.debug_if
      f7_fetch_bundle.bp_xcpt_if_oh (i) := bpu.io.xcpt_if

      redirect_found = redirect_found || f7_redirects(i)
    }
    last_inst = bank_insts(bankWidth-1)(15,0)
    bank_prev_is_half = Mux(f7_bank_mask(b),
      (!(bank_mask(bankWidth-2) && !isRVC(bank_insts(bankWidth-2))) && !isRVC(last_inst)),
      bank_prev_is_half)
    bank_prev_half    = Mux(f7_bank_mask(b),
      last_inst(15,0),
      bank_prev_half)
  }

  f7_fetch_bundle.cfi_type      := f7_cfi_types(f7_fetch_bundle.cfi_idx.bits)
  f7_fetch_bundle.cfi_is_call   := f7_call_mask(f7_fetch_bundle.cfi_idx.bits)
  f7_fetch_bundle.cfi_is_ret    := f7_ret_mask (f7_fetch_bundle.cfi_idx.bits)
  f7_fetch_bundle.cfi_npc_plus4 := f7_npc_plus4_mask(f7_fetch_bundle.cfi_idx.bits)

  f7_fetch_bundle.ghist    := f7.io.deq.bits.ghist
  f7_fetch_bundle.lhist    := f7_bpd_resp.io.deq.bits.lhist
  f7_fetch_bundle.bpd_meta := f7_bpd_resp.io.deq.bits.meta

  f7_fetch_bundle.end_half.valid := bank_prev_is_half
  f7_fetch_bundle.end_half.bits  := bank_prev_half

  when (f7.io.deq.fire) {
    f7_prev_is_half := bank_prev_is_half
    f7_prev_half    := bank_prev_half
    assert(f7_bpd_resp.io.deq.bits.pc === f7_fetch_bundle.pc)
  }

  when (f7_clear) {
    f7_prev_is_half := false.B
  }

  f7_fetch_bundle.cfi_idx.valid := f7_redirects.reduce(_||_)
  f7_fetch_bundle.cfi_idx.bits  := PriorityEncoder(f7_redirects)

  f7_fetch_bundle.ras_top := f7_imemresp.ras_resp
  // Redirect earlier stages only if the later stage
  // can consume this packet

  val f7_predicted_target = Mux(f7_redirects.reduce(_||_),
    Mux(f7_fetch_bundle.cfi_is_ret && useBPD.B && useRAS.B,
      ras.io.read_addr,
      f7_targs(PriorityEncoder(f7_redirects))
    ),
    nextFetch(f7_fetch_bundle.pc)
  )

  f7_fetch_bundle.next_pc       := f7_predicted_target
  val f7_predicted_ghist = f7_fetch_bundle.ghist.update(
    f7_fetch_bundle.br_mask,
    f7_fetch_bundle.cfi_idx.valid,
    f7_fetch_bundle.br_mask(f7_fetch_bundle.cfi_idx.bits),
    f7_fetch_bundle.cfi_idx.bits,
    f7_fetch_bundle.cfi_idx.valid,
    f7_fetch_bundle.pc,
    f7_fetch_bundle.cfi_is_call,
    f7_fetch_bundle.cfi_is_ret
  )


  ras.io.write_valid := false.B
  ras.io.write_addr  := f7_aligned_pc + (f7_fetch_bundle.cfi_idx.bits << 1) + Mux(
    f7_fetch_bundle.cfi_npc_plus4, 4.U, 2.U)
  ras.io.write_idx   := WrapInc(f7_fetch_bundle.ghist.ras_idx, nRasEntries)


  val f7_correct_f1_ghist = f7_imemresp.bpd_f1_ghist =/= f7_predicted_ghist && enableGHistStallRepair.B
  val f7_correct_f2_ghist = f7_imemresp.bpd_f2_ghist =/= f7_predicted_ghist && enableGHistStallRepair.B

  when (f7.io.deq.valid && f8_ready) {
    when (f7_fetch_bundle.cfi_is_call && f7_fetch_bundle.cfi_idx.valid) {
      ras.io.write_valid := true.B
    }
    when (f7_redirects.reduce(_||_)) {
      f7_prev_is_half := false.B
    }
    
    when (f7_imemresp.bpd_f2_valid && f7_imemresp.bpd_f2_vpc === f7_predicted_target && !f7_correct_f2_ghist) {
      f7.io.enq.bits.ghist := f7_predicted_ghist
    } .elsewhen (!f7_imemresp.bpd_f2_valid && f7_imemresp.bpd_f1_valid && f7_imemresp.bpd_f1_vpc === f7_predicted_target && !f7_correct_f1_ghist) {
      f6_ghist := f7_predicted_ghist
    } .elsewhen ((f7_imemresp.bpd_f2_valid && (f7_imemresp.bpd_f2_vpc =/= f7_predicted_target || f7_correct_f2_ghist)) ||
          (!f7_imemresp.bpd_f2_valid && f7_imemresp.bpd_f1_valid && (f7_imemresp.bpd_f1_vpc =/= f7_predicted_target || f7_correct_f1_ghist)) ||
          (!f7_imemresp.bpd_f2_valid && !f7_imemresp.bpd_f1_valid)) {
      f2_clear := true.B
      f1_clear := true.B
      f3_clear := true.B
      f5_clear := true.B
      f6_clear := true.B
      f4_valid := false.B

      s0_valid     := !(f7_fetch_bundle.xcpt_pf_if || f7_fetch_bundle.xcpt_ae_if)
      s0_vpc       := f7_predicted_target
      s0_ghist     := f7_predicted_ghist
      s0_tsrc      := BSRC_3
      f4_is_replay := false.B

      f7_fetch_bundle.fsrc := BSRC_3
      // printf("Cycle %d f7 redirect %x by %x\n", debug_cycles.value, f7_predicted_target, f7_imemresp.pc)
    }
  }
  
  // printf("fetch_bundle_insts: %x\t%x\t%x\t%x\n", f7_fetch_bundle.insts(0), f7_fetch_bundle.insts(1), f7_fetch_bundle.insts(2), f7_fetch_bundle.insts(3))
  // printf("fetch_bundle_exp_insts: %x\t%x\t%x\t%x\n", f7_fetch_bundle.exp_insts(0), f7_fetch_bundle.exp_insts(1), f7_fetch_bundle.exp_insts(2), f7_fetch_bundle.exp_insts(3))

  // When f3 finds a btb mispredict, queue up a bpd correction update
  val f4_btb_corrections = Module(new Queue(new BranchPredictionUpdate, 2))
  f4_btb_corrections.io.enq.valid := f7.io.deq.fire && f7_btb_mispredicts.reduce(_||_) && enableBTBFastRepair.B
  f4_btb_corrections.io.enq.bits  := DontCare
  f4_btb_corrections.io.enq.bits.is_mispredict_update := false.B
  f4_btb_corrections.io.enq.bits.is_repair_update     := false.B
  f4_btb_corrections.io.enq.bits.btb_mispredicts      := f7_btb_mispredicts.asUInt
  f4_btb_corrections.io.enq.bits.pc                   := f7_fetch_bundle.pc
  f4_btb_corrections.io.enq.bits.ghist                := f7_fetch_bundle.ghist
  f4_btb_corrections.io.enq.bits.lhist                := f7_fetch_bundle.lhist
  f4_btb_corrections.io.enq.bits.meta                 := f7_fetch_bundle.bpd_meta


  // -------------------------------------------------------
  // **** F4 ****
  // -------------------------------------------------------
  val f4_clear = WireInit(false.B)
  val f4 = withReset(reset.asBool || f4_clear) {
    Module(new Queue(new FetchBundle, 1, pipe=true, flow=false))}

  val fb  = Module(new FetchBuffer)
  val ftq = Module(new FetchTargetQueue)

  // When we mispredict, we need to repair

  // Deal with sfbs
  val f4_shadowable_masks = VecInit((0 until fetchWidth) map { i =>
     f4.io.deq.bits.shadowable_mask.asUInt |
    ~f4.io.deq.bits.sfb_masks(i)(fetchWidth-1,0)
  })
  val f3_shadowable_masks = VecInit((0 until fetchWidth) map { i =>
    Mux(f4.io.enq.valid, f4.io.enq.bits.shadowable_mask.asUInt, 0.U) |
    ~f4.io.deq.bits.sfb_masks(i)(2*fetchWidth-1,fetchWidth)
  })
  val f4_sfbs = VecInit((0 until fetchWidth) map { i =>
    enableSFBOpt.B &&
    ((~f4_shadowable_masks(i) === 0.U) &&
     (~f3_shadowable_masks(i) === 0.U) &&
     f4.io.deq.bits.sfbs(i) &&
     !(f4.io.deq.bits.cfi_idx.valid && f4.io.deq.bits.cfi_idx.bits === i.U) &&
      Mux(f4.io.deq.bits.sfb_dests(i) === 0.U,
        !bank_prev_is_half,
      Mux(f4.io.deq.bits.sfb_dests(i) === fetchBytes.U,
        !f4.io.deq.bits.end_half.valid,
        true.B)
      )

     )
  })
  val f4_sfb_valid = f4_sfbs.reduce(_||_) && f4.io.deq.valid
  val f4_sfb_idx   = PriorityEncoder(f4_sfbs)
  val f4_sfb_mask  = f4.io.deq.bits.sfb_masks(f4_sfb_idx)
  // If we have a SFB, wait for next fetch to be available in f3
  val f4_delay     = (
    f4.io.deq.bits.sfbs.reduce(_||_) &&
    !f4.io.deq.bits.cfi_idx.valid &&
    !f4.io.enq.valid &&
    !f4.io.deq.bits.xcpt_pf_if &&
    !f4.io.deq.bits.xcpt_ae_if
  )
  when (f4_sfb_valid) {
    f7_shadowed_mask := f4_sfb_mask(2*fetchWidth-1,fetchWidth).asBools
  } .otherwise {
    f7_shadowed_mask := VecInit(0.U(fetchWidth.W).asBools)
  }

  f8_ready := f4.io.enq.ready
  f4.io.enq.valid := f7.io.deq.valid && !f7_clear
  f4.io.enq.bits  := f7_fetch_bundle
  f4.io.deq.ready := fb.io.enq.ready && ftq.io.enq.ready && !f4_delay

  /*
  when (f4.io.enq.valid) {
    printf("Cycle %d f8 enq %x\n", debug_cycles.value, f4.io.enq.bits.pc)
  }
  */
  

  fb.io.enq.valid := f4.io.deq.valid && ftq.io.enq.ready && !f4_delay
  fb.io.enq.bits  := f4.io.deq.bits
  fb.io.enq.bits.ftq_idx := ftq.io.enq_idx
  fb.io.enq.bits.sfbs    := Mux(f4_sfb_valid, UIntToOH(f4_sfb_idx), 0.U(fetchWidth.W)).asBools
  fb.io.enq.bits.shadowed_mask := (
    Mux(f4_sfb_valid, f4_sfb_mask(fetchWidth-1,0), 0.U(fetchWidth.W)) |
    f4.io.deq.bits.shadowed_mask.asUInt
  ).asBools

  /*
  when (fb.io.enq.valid) {
    printf("Cycle %d fetch buffer %x %x %x %x %x\n", debug_cycles.value, fb.io.enq.bits.pc, 
    fb.io.enq.bits.exp_insts(0), 
    fb.io.enq.bits.exp_insts(1), 
    fb.io.enq.bits.exp_insts(2), 
    fb.io.enq.bits.exp_insts(3))
  }
  */
  
  


  ftq.io.enq.valid          := f4.io.deq.valid && fb.io.enq.ready && !f4_delay
  ftq.io.enq.bits           := f4.io.deq.bits

  val bpd_update_arbiter = Module(new Arbiter(new BranchPredictionUpdate, 2))
  bpd_update_arbiter.io.in(0).valid := ftq.io.bpdupdate.valid
  bpd_update_arbiter.io.in(0).bits  := ftq.io.bpdupdate.bits
  assert(bpd_update_arbiter.io.in(0).ready)
  bpd_update_arbiter.io.in(1) <> f4_btb_corrections.io.deq
  bpd.io.update := bpd_update_arbiter.io.out
  bpd_update_arbiter.io.out.ready := true.B

  when (ftq.io.ras_update && enableRasTopRepair.B) {
    ras.io.write_valid := true.B
    ras.io.write_idx   := ftq.io.ras_update_idx
    ras.io.write_addr  := ftq.io.ras_update_pc
  }


  // -------------------------------------------------------
  // **** To Core (F5) ****
  // -------------------------------------------------------

  io.cpu.fetchpacket <> fb.io.deq
  io.cpu.get_pc <> ftq.io.get_ftq_pc
  ftq.io.deq := io.cpu.commit
  ftq.io.brupdate := io.cpu.brupdate

  ftq.io.redirect.valid   := io.cpu.redirect_val
  ftq.io.redirect.bits    := io.cpu.redirect_ftq_idx
  fb.io.clear := false.B

  when (io.cpu.sfence.valid) {
    fb.io.clear := true.B
    f7_clear    := true.B
    f6_clear    := true.B
    f5_clear    := true.B
    f4_clear    := true.B
    f3_clear    := true.B
    f2_clear    := true.B
    f1_clear    := true.B
    f4_valid    := false.B

    s0_valid     := false.B
    f4_valid     := false.B
    s0_vpc       := io.cpu.sfence.bits.addr
    f4_vpc       := io.cpu.sfence.bits.addr
    f4_is_replay := false.B
    f4_is_sfence := true.B
    // printf("sfence redirect to %x\n", io.cpu.redirect_pc)

  }.elsewhen (io.cpu.redirect_flush) {
    fb.io.clear := true.B
    f7_clear    := true.B
    f6_clear    := true.B
    f5_clear    := true.B
    f4_clear    := true.B
    f3_clear    := true.B
    f2_clear    := true.B
    f1_clear    := true.B
    f4_valid    := false.B

    f7_prev_is_half := false.B

    s0_valid     := io.cpu.redirect_val
    s0_vpc       := io.cpu.redirect_pc
    s0_ghist     := io.cpu.redirect_ghist
    s0_tsrc      := BSRC_C
    f4_is_replay := false.B

    ftq.io.redirect.valid := io.cpu.redirect_val
    ftq.io.redirect.bits  := io.cpu.redirect_ftq_idx

    // printf("Cycle %d flush redirect to %x\n", debug_cycles.value, io.cpu.redirect_pc)
  }

  ftq.io.debug_ftq_idx := io.cpu.debug_ftq_idx
  io.cpu.debug_fetch_pc := ftq.io.debug_fetch_pc


  override def toString: String =
    (BoomCoreStringPrefix("====Overall Frontend Params====") + "\n"
    + icache.toString + bpd.toString)
}
