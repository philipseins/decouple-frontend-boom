package boom.ifu

import chisel3._
import chisel3.util._

import freechips.rocketchip.config.{Parameters}
import freechips.rocketchip.rocket.{MStatus, BP, BreakpointUnit}
import freechips.rocketchip.util.{Str}

import boom.common._
import boom.exu._
import boom.util._

case class PtqParameters(
    nEntries: Int = 16
)

class PredictTargetQueue(implicit p: Parameters) extends BoomModule
  with HasBoomCoreParameters
  with HasBoomFrontendParameters
{
    val num_entries = ptqSz

    val debug_cycles = freechips.rocketchip.util.WideCounter(32)
    
    val io = IO(new BoomBundle {
        val enq = Flipped(Decoupled(new PredictBundle()))
        val deq = new DecoupledIO(new PredictBundle())
        val read = new DecoupledIO(new PredictBundle())
        val clear = Input(Bool())
        val reset = Input(Bool())
        val count = Output(UInt(log2Ceil(num_entries + 1).W))
    })
    val ram = Mem(num_entries, new PredictBundle)
    val enq_ptr = RegInit(0.U(log2Ceil(num_entries).W))
    val deq_ptr = RegInit(0.U(log2Ceil(num_entries).W))
    val read_ptr  = RegInit(0.U(log2Ceil(num_entries).W))
    val ptr_match = enq_ptr === deq_ptr
    val maybe_full = RegInit(false.B)
    val empty = ptr_match && !maybe_full
    val full = ptr_match && maybe_full
    val read_enable = read_ptr === enq_ptr
    val do_enq = WireDefault(io.enq.fire)
    val do_deq = WireDefault(io.deq.fire)
    val read_next = WireDefault(io.read.fire)

    when (do_enq) {
      ram(enq_ptr) := io.enq.bits
      enq_ptr := WrapInc(enq_ptr, num_entries)
    }

    when (do_deq && (deq_ptr =/= read_ptr || full)) {
      deq_ptr := WrapInc(deq_ptr, num_entries)
    }
    
    when (read_next) {
      read_ptr := WrapInc(read_ptr, num_entries)
      // printf("Cycle %d read_ptr inc\n", debug_cycles.value)
    }

    when (do_enq =/= do_deq) {
      maybe_full := do_enq
    }

    when (io.reset) {
      read_ptr := WrapInc(deq_ptr, num_entries)
      // printf("Cycle %d reset ptq\n", debug_cycles.value)
    }

    when (io.clear) {
      enq_ptr := 0.U
      deq_ptr := 0.U
      read_ptr := 0.U
      maybe_full := false.B
      // printf("Cycle %d clear ptq\n", debug_cycles.value)
    }

    io.deq.valid := !empty
    io.read.valid  := !read_enable
    io.enq.ready := !full

    io.deq.bits := ram(deq_ptr)
    io.read.bits  := ram(read_ptr)

    /*
    printf("Cycle %d enq_ptr: %d, deq_ptr: %d, read_ptr: %d\n", debug_cycles.value, enq_ptr, deq_ptr, read_ptr)
    for (i <- 0 until num_entries) {
      val ptqpc = ram(i).pc
      printf("Cycle %d PTQ entry %d: %x\n", debug_cycles.value, i.U(log2Ceil(num_entries).W), ptqpc)
    }
    */
    val ptr_diff = enq_ptr - deq_ptr
    io.count := Mux(maybe_full && ptr_match, num_entries.U, 0.U) | ptr_diff
}