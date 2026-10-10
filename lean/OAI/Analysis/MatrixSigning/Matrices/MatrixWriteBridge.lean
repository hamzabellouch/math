import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.DenseMatrixUpdate
import OAI.Analysis.MatrixSigning.Encoding.FramedArrayReplacement

namespace OAI

namespace KS.W08

open KS.W07 KS.W29.FixedSequential
open KS.W11.FramedArrayRewrite

theorem run_denseMatrix_replace {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) (q : ℚ)
    (tail bits : List Bool)
    (hlen : 2 * (denseMatrixTape M ++ tail).length +
      2 * (KS.W01.frame (KS.W01.encodeRat q)).length + i.val * n + j.val + 3 ≤ bits.length) :
    program.toMachine.run
      (config (some program.initial) (denseMatrixTape M ++ tail)
        (KS.W01.frame (KS.W01.encodeRat q)) [] [] (denseMatrixCursor i j)) bits =
      config none (denseMatrixTape (denseMatrixSet M i j q) ++ tail) [] [] [] [] := by
  have hi : i.val * n + j.val < (denseMatrixPayloads M).length := by
    rw [denseMatrixPayloads_length]
    exact matrixEntryIndex_lt i j
  have h := run_replace (denseMatrixPayloads M) (i.val * n + j.val) hi
    (KS.W01.encodeRat q) tail bits (by simpa only [denseMatrixTape, Nat.add_assoc] using hlen)
  simpa only [denseMatrixTape, denseMatrixCursor, denseMatrixPayloads_set] using h

theorem denseMatrix_replace_time {n : ℕ} (M : DenseRatMatrix n) (b c : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (q : ℚ) (hqnum : q.num.natAbs ≤ 2 ^ c) (hqden : q.den ≤ 2 ^ c) :
    HaltsFromWithin program
      (config (some program.initial) (denseMatrixTape M)
        (KS.W01.frame (KS.W01.encodeRat q)) [] [] (denseMatrixCursor i j))
      (n * n * (16 * b + 31) + 16 * c + 33) := by
  intro bits hlen
  have ht := denseMatrixTape_length_le M b hnum hden
  have hi := (matrixEntryIndex_lt i j).le
  have hq := KS.W01.ratLength_le_of_parts q c c hqnum hqden
  have hf : (KS.W01.frame (KS.W01.encodeRat q)).length ≤ 8 * c + 15 := by
    rw [KS.W01.length_frame]
    unfold KS.W01.ratLength at hq
    omega
  have hb : 2 * (denseMatrixTape M ++ []).length +
      2 * (KS.W01.frame (KS.W01.encodeRat q)).length + i.val * n + j.val + 3 ≤ bits.length := by
    rw [List.append_nil, hlen]
    calc
      _ ≤ 2 * (n * n * (8 * b + 15)) + 2 * (8 * c + 15) + n * n + 3 := by omega
      _ = _ := by ring
  have h := run_denseMatrix_replace M i j q [] bits hb
  have hs := congrArg (fun c => c.state) h
  simp only [List.append_nil] at hs
  exact hs

end KS.W08

end OAI
