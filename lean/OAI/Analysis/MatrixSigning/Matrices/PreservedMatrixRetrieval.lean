import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.ReusableArrayLookup
import OAI.Analysis.MatrixSigning.Matrices.DenseMatrixSerialization
import OAI.Analysis.MatrixSigning.Complexity.StorageCost

namespace OAI

namespace KS.W08

open KS.W07 KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup

theorem run_preservedMatrix_lookup {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n)
    (tail bits : List Bool)
    (hlen : 5 * (denseMatrixTape M ++ tail).length + i.val * n + j.val + 4 ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, arrayStacks (denseMatrixTape M ++ tail)
        [] [] [] (denseMatrixCursor i j)⟩ bits =
      ⟨none, arrayStacks (denseMatrixTape M ++ tail) []
        (KS.W01.encodeRat (AccessCounted.readMatrix M i j).value) [] []⟩ := by
  have hi : i.val * n + j.val < (denseMatrixPayloads M).length := by
    rw [denseMatrixPayloads_length]
    exact matrixEntryIndex_lt i j
  have h := run_program (denseMatrixPayloads M) (i.val * n + j.val) hi tail bits
    (by simpa only [denseMatrixTape, Nat.add_assoc] using hlen)
  simpa only [denseMatrixTape, denseMatrixCursor, denseMatrixPayloads_get,
    AccessCounted.readMatrix_value] using h

theorem preservedMatrix_lookup_time {n : ℕ} (M : DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) (i j : Fin n) :
    HaltsFromWithin program
      ⟨some program.initial, arrayStacks (denseMatrixTape M) [] [] [] (denseMatrixCursor i j)⟩
      (n * n * (40 * b + 76) + 4) := by
  intro bits hlen
  have ht := denseMatrixTape_length_le M b hnum hden
  have hi := (matrixEntryIndex_lt i j).le
  have hb : 5 * (denseMatrixTape M ++ []).length + i.val * n + j.val + 4 ≤
      bits.length := by
    rw [List.append_nil, hlen]
    calc
      _ ≤ 5 * (n * n * (8 * b + 15)) + n * n + 4 := by omega
      _ = _ := by ring
  have h := run_preservedMatrix_lookup M i j [] bits hb
  simp only [List.append_nil] at h
  exact congrArg (fun c => c.state) h

end KS.W08

end OAI
