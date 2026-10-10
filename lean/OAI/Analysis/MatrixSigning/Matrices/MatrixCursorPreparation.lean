import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnary
import OAI.Analysis.MatrixSigning.Matrices.DenseMatrixSerialization

namespace OAI

section

namespace KS.W08

def denseMatrixBinaryCursor {n : ℕ} (i j : Fin n) : List Bool :=
  Computability.encodeNat (i.val * n + j.val)

@[simp] theorem denseMatrixBinaryCursor_value {n : ℕ} (i j : Fin n) :
    KS.W19.bitsValue (denseMatrixBinaryCursor i j) = i.val * n + j.val := by
  simp [denseMatrixBinaryCursor, KS.W19.bitsValue_encodeNat]

theorem denseMatrixBinaryCursor_length_le {n : ℕ} (i j : Fin n) :
    (denseMatrixBinaryCursor i j).length ≤ i.val * n + j.val := by
  change KS.W01.natPayloadLength (i.val * n + j.val) ≤ _
  rw [KS.W01.natPayloadLength_eq_size]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem run_denseMatrix_cursor {n : ℕ} (i j : Fin n) (bits : List Bool)
    (hlen : 8 * n * n + 2 ≤ bits.length) :
    KS.W03.BinaryToUnary.machine.run
      (KS.W03.BinaryToUnary.machine.init (denseMatrixBinaryCursor i j)) bits =
      KS.W03.BinaryToUnary.cfg none [] (denseMatrixCursor i j) [] := by
  have hi := (matrixEntryIndex_lt i j).le
  have hl := denseMatrixBinaryCursor_length_le i j
  have hb : 4 * KS.W19.bitsValue (denseMatrixBinaryCursor i j) +
      4 * (denseMatrixBinaryCursor i j).length + 2 ≤ bits.length := by
    rw [denseMatrixBinaryCursor_value]
    nlinarith
  simpa only [denseMatrixBinaryCursor_value, denseMatrixCursor] using
    KS.W03.BinaryToUnary.run_input_linear (denseMatrixBinaryCursor i j) bits hb

theorem denseMatrix_cursor_halts {n : ℕ} (i j : Fin n) :
    KS.W03.BinaryToUnary.machine.HaltsWithin (denseMatrixBinaryCursor i j) (8 * n * n + 2) := by
  intro seed
  change (KS.W03.BinaryToUnary.machine.run
    (KS.W03.BinaryToUnary.machine.init (denseMatrixBinaryCursor i j)) (List.ofFn seed)).state = none
  rw [run_denseMatrix_cursor i j (List.ofFn seed) (by simp)]
  rfl

end KS.W08

end

end OAI
