import Mathlib
import OAI.Analysis.MatrixSigning.Machines.StackTransferSpecs
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationLoop
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationNormalize
import OAI.Analysis.MatrixSigning.Encoding.ReusableArrayLookup
import OAI.Analysis.MatrixSigning.Arithmetic.FixedBinaryAdder
import OAI.Analysis.MatrixSigning.Matrices.MatrixCursorPreparation

namespace OAI

namespace KS.W08.MatrixAddress

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody KS.W03.BinaryAccumulator

def addPorts : Fin 3 ↪ Fin 7 := ⟨![0, 3, 4], by decide⟩
def addProgram : Program 7 := KS.W01.FixedBinaryAdder.program addPorts

def cleanupProgram : Program 7 := KS.W04.ReusableArrayLookup.reoutput
  (KS.W04.BinaryStackMoves.clearProgram 2) 3

def program : Program 7 := compose
  (compose (compose KS.W03.MultiplicationLoop.program addProgram)
    KS.W03.MultiplicationNormalize.program) cleanupProgram

def rawProduct (row dim : List Bool) : List Bool := loop row dim []
def rawAddress (row dim col : List Bool) : List Bool :=
  KS.W01.FixedBinaryAdder.result col (rawProduct row dim)

def ticks (row dim col : List Bool) : ℕ :=
  ((loopTicks row dim [] + (2 * (col.length + (rawProduct row dim).length) + 3)) +
    (2 * (rawAddress row dim col).length + 2)) +
    ((KS.W03.MultiplicationLoop.advance row dim).length + 1)

theorem add_spec (col operand product : List Bool) :
    RunSpec addProgram (registers col [] operand product [] [] [])
      (registers [] [] operand (KS.W01.FixedBinaryAdder.result col product) [] [] [])
      (2 * (col.length + product.length) + 3) := by
  have h := KS.W01.FixedBinaryAdder.runSpec_linear addPorts
    (registers col [] operand product [] [] []) col product rfl rfl rfl
  have he : KS.W01.FixedBinaryAdder.output addPorts
      (registers col [] operand product [] [] []) col product =
      registers [] [] operand (KS.W01.FixedBinaryAdder.result col product) [] [] [] := by
    funext j
    fin_cases j <;> simp [KS.W01.FixedBinaryAdder.output, addPorts, registers, Function.update]
  rw [he] at h
  exact h

private theorem reoutput_spec {k : ℕ} (P : Program k) (port : Fin k)
    (before after : Fin k → List Bool) (fuel : ℕ) (h : RunSpec P before after fuel) :
    RunSpec (KS.W04.ReusableArrayLookup.reoutput P port) before after fuel := by
  intro bits hbits
  erw [KS.W04.ReusableArrayLookup.run_reoutput]
  exact h bits hbits

theorem cleanup_spec (operand address : List Bool) :
    RunSpec cleanupProgram (registers [] [] operand address [] [] [])
      (registers [] [] [] address [] [] []) (operand.length + 1) := by
  apply reoutput_spec
  have h:=KS.W15.RationalMultiply.clear_spec (2 : Fin 7)
    (registers [] [] operand address [] [] [])
  have he : KS.W15.RationalMultiply.clearAfter 2 (registers [] [] operand address [] [] []) =
      registers [] [] [] address [] [] [] := by
    funext j
    fin_cases j <;> simp [KS.W15.RationalMultiply.clearAfter,registers]
  rw [he] at h
  exact h

theorem full_spec (row dim col : List Bool) :
    RunSpec program (registers col row dim [] [] [] [])
      (registers [] [] [] (Computability.encodeNat
        (KS.W19.bitsValue row * KS.W19.bitsValue dim + KS.W19.bitsValue col)) [] [] [])
      (ticks row dim col) := by
  have hm := KS.W03.MultiplicationLoop.loop_spec col row dim []
  have ha := add_spec col (KS.W03.MultiplicationLoop.advance row dim) (rawProduct row dim)
  have hn := KS.W03.MultiplicationNormalize.normalize_spec [] []
    (KS.W03.MultiplicationLoop.advance row dim) (rawAddress row dim col)
  have hc := cleanup_spec (KS.W03.MultiplicationLoop.advance row dim)
    (Computability.encodeNat (KS.W19.bitsValue (rawAddress row dim col)))
  have h := ((hm.compose ha).compose hn).compose hc
  have hv : KS.W19.bitsValue (rawAddress row dim col) =
      KS.W19.bitsValue row * KS.W19.bitsValue dim + KS.W19.bitsValue col := by
    rw [rawAddress, KS.W01.FixedBinaryAdder.result_value, rawProduct, loop_zero_correct]
    omega
  rw [hv] at h
  exact h

theorem ticks_le (row dim col : List Bool) :
    ticks row dim col ≤ 32 * (row.length + dim.length + col.length + 1) ^ 2 := by
  have hm := loop_zero_ticks_le row dim
  have hp := loop_zero_length_le row dim
  have ha := KS.W01.BinaryAdder.addBits_length_le false col (rawProduct row dim)
  have hc := KS.W03.MultiplicationLoop.advance_length row dim
  have hmax : max col.length (rawProduct row dim).length ≤
      col.length + (rawProduct row dim).length := by omega
  unfold ticks rawAddress KS.W01.FixedBinaryAdder.result
  change (rawProduct row dim).length ≤ row.length + dim.length at hp
  nlinarith [Nat.le_max_left col.length (rawProduct row dim).length,
    Nat.le_max_right col.length (rawProduct row dim).length,
    hmax,
    Nat.zero_le (row.length * col.length), Nat.zero_le (dim.length * col.length)]

theorem run_encoded (row dim col : ℕ) (bits : List Bool)
    (hlen : 32 * (Nat.size row + Nat.size dim + Nat.size col + 1) ^ 2 ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, registers (Computability.encodeNat col)
        (Computability.encodeNat row) (Computability.encodeNat dim) [] [] [] []⟩ bits =
      ⟨none, registers [] [] [] (Computability.encodeNat (row * dim + col)) [] [] []⟩ := by
  have h := full_spec (Computability.encodeNat row) (Computability.encodeNat dim)
    (Computability.encodeNat col)
  have hb := ticks_le (Computability.encodeNat row) (Computability.encodeNat dim)
    (Computability.encodeNat col)
  have hr : (Computability.encodeNat row).length = Nat.size row := KS.W01.natPayloadLength_eq_size row
  have hd : (Computability.encodeNat dim).length = Nat.size dim := KS.W01.natPayloadLength_eq_size dim
  have hc : (Computability.encodeNat col).length = Nat.size col := KS.W01.natPayloadLength_eq_size col
  rw [hr, hd, hc] at hb
  simpa only [KS.W19.bitsValue_encodeNat] using h.run_of_le bits (hb.trans hlen)

theorem matrix_address_budget {n : ℕ} (i j : Fin n) :
    32 * (Nat.size i.val + Nat.size n + Nat.size j.val + 1) ^ 2 ≤ 512 * (n + 1) ^ 2 := by
  have hi : Nat.size i.val ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans i.isLt.le
  have hj : Nat.size j.val ≤ n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans j.isLt.le
  have hn : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have h : Nat.size i.val + Nat.size n + Nat.size j.val + 1 ≤ 4 * (n + 1) := by omega
  have hs := Nat.pow_le_pow_left h 2
  nlinarith

theorem run_matrix_address {n : ℕ} (i j : Fin n) (bits : List Bool)
    (hlen : 512 * (n + 1) ^ 2 ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, registers (Computability.encodeNat j.val)
        (Computability.encodeNat i.val) (Computability.encodeNat n) [] [] [] []⟩ bits =
      ⟨none, registers [] [] [] (KS.W08.denseMatrixBinaryCursor i j) [] [] []⟩ := by
  simpa only [KS.W08.denseMatrixBinaryCursor] using
    run_encoded i.val n j.val bits ((matrix_address_budget i j).trans hlen)

end KS.W08.MatrixAddress

end OAI
