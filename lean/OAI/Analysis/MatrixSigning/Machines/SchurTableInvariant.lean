import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalExpressionHeight
import OAI.Analysis.MatrixSigning.Matrices.MatrixWriteBridge

namespace OAI

namespace KS.W07.SchurTable

open KS.W08 KS.W17

def partialMatrix {n : ℕ} (M : DenseRatMatrix (n + 1)) (s : ℕ) : DenseRatMatrix n :=
  DenseRatMatrix.ofMatrix (fun i j =>
    if i.val * n + j.val < s then schurTail (DenseRatMatrix.decode M) i j else 0)

@[simp] theorem partialMatrix_decode {n : ℕ} (M : DenseRatMatrix (n + 1))
    (s : ℕ) (i j : Fin n) :
    (partialMatrix M s).decode i j =
      if i.val * n + j.val < s then schurTail M.decode i j else 0 :=
  congrFun (congrFun (DenseRatMatrix.decode_ofMatrix _) i) j

@[simp] theorem partial_zero {n : ℕ} (M : DenseRatMatrix (n + 1)) :
    partialMatrix M 0 = DenseRatMatrix.ofMatrix 0 := by
  apply congrArg DenseRatMatrix.ofMatrix
  funext i j
  simp

theorem partial_complete {n : ℕ} (M : DenseRatMatrix (n + 1)) :
    partialMatrix M (n * n) = DenseRatMatrix.ofMatrix (schurTail (DenseRatMatrix.decode M)) := by
  apply congrArg DenseRatMatrix.ofMatrix
  funext i j
  simp [matrixEntryIndex_lt]

theorem partial_set {n : ℕ} (M : DenseRatMatrix (n + 1)) (i j : Fin n) :
    denseMatrixSet (partialMatrix M (i.val * n + j.val)) i j
        (schurTail (DenseRatMatrix.decode M) i j) =
      partialMatrix M (i.val * n + j.val + 1) := by
  have he : ∀ k l : Fin n,
      (i = k ∧ j = l) ↔ i.val * n + j.val = k.val * n + l.val := by
    intro k l
    simpa [matrixEntryIndex, Nat.mul_comm, Nat.add_comm] using
      matrixEntryIndex_eq_iff i j (matrixEntryIndex k l)
  have hdecode : DenseRatMatrix.decode
      (denseMatrixSet (partialMatrix M (i.val * n + j.val)) i j
        (schurTail (DenseRatMatrix.decode M) i j)) =
      DenseRatMatrix.decode (partialMatrix M (i.val * n + j.val + 1)) := by
    funext k l
    rw [denseMatrixSet_decode]
    simp only [partialMatrix_decode]
    by_cases hkl : i = k ∧ j = l
    · rcases hkl with ⟨rfl, rfl⟩
      simp
    · have hne : i.val * n + j.val ≠ k.val * n + l.val :=
        fun h => hkl ((he k l).mpr h)
      have hlt : k.val * n + l.val < i.val * n + j.val + 1 ↔
          k.val * n + l.val < i.val * n + j.val := by omega
      simp [hkl, hlt]
  calc
    _ = DenseRatMatrix.ofMatrix (DenseRatMatrix.decode
        (denseMatrixSet (partialMatrix M (i.val * n + j.val)) i j
          (schurTail (DenseRatMatrix.decode M) i j))) :=
      (DenseRatMatrix.ofMatrix_decode _).symm
    _ = DenseRatMatrix.ofMatrix (DenseRatMatrix.decode
        (partialMatrix M (i.val * n + j.val + 1))) := congrArg DenseRatMatrix.ofMatrix hdecode
    _ = _ := DenseRatMatrix.ofMatrix_decode _

theorem run_write_partial {n : ℕ} (M : DenseRatMatrix (n + 1)) (i j : Fin n)
    (tail bits : List Bool)
    (hlen : 2 * (denseMatrixTape (partialMatrix M (i.val * n + j.val)) ++ tail).length +
      2 * (KS.W01.frame (KS.W01.encodeRat (schurTail (DenseRatMatrix.decode M) i j))).length +
      i.val * n + j.val + 3 ≤ bits.length) :
    KS.W11.FramedArrayRewrite.program.toMachine.run
      (KS.W11.FramedArrayRewrite.config (some KS.W11.FramedArrayRewrite.program.initial)
        (denseMatrixTape (partialMatrix M (i.val * n + j.val)) ++ tail)
        (KS.W01.frame (KS.W01.encodeRat (schurTail (DenseRatMatrix.decode M) i j)))
        [] [] (denseMatrixCursor i j)) bits =
      KS.W11.FramedArrayRewrite.config none
        (denseMatrixTape (partialMatrix M (i.val * n + j.val + 1)) ++ tail) [] [] [] [] := by
  simpa [partial_set] using run_denseMatrix_replace (partialMatrix M (i.val * n + j.val))
    i j (schurTail (DenseRatMatrix.decode M) i j) tail bits hlen

theorem entry_parts_le {n : ℕ} (M : DenseRatMatrix (n + 1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) (i j : Fin n) :
    (schurTail (DenseRatMatrix.decode M) i j).num.natAbs ≤ 2 ^ (4 * b + 3) ∧
      (schurTail (DenseRatMatrix.decode M) i j).den ≤ 2 ^ (4 * b + 3) := by
  have hb : (schurEntryExpr (DenseRatMatrix.decode M) i j).inputsBounded b :=
    ⟨⟨hnum _ _, hden _ _⟩, ⟨⟨⟨hnum _ _, hden _ _⟩, ⟨hnum _ _, hden _ _⟩⟩,
      ⟨hnum _ _, hden _ _⟩⟩⟩
  have h := (schurEntryExpr (DenseRatMatrix.decode M) i j).eval_parts_le b hb
  simp [schurEntryExpr, RationalExpr.leaves, RationalExpr.operations] at h
  exact h

theorem partial_parts_le {n : ℕ} (M : DenseRatMatrix (n + 1)) (b s : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) (i j : Fin n) :
    (DenseRatMatrix.decode (partialMatrix M s) i j).num.natAbs ≤ 2 ^ (4 * b + 3) ∧
      (DenseRatMatrix.decode (partialMatrix M s) i j).den ≤ 2 ^ (4 * b + 3) := by
  simp only [partialMatrix_decode]
  split_ifs
  · exact entry_parts_le M b hnum hden i j
  · have hp : 1 ≤ 2 ^ (4 * b + 3) := Nat.one_le_pow _ _ (by decide)
    simpa using hp

theorem write_partial_time {n : ℕ} (M : DenseRatMatrix (n + 1)) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) (i j : Fin n) :
    KS.W29.FixedSequential.HaltsFromWithin KS.W11.FramedArrayRewrite.program
      (KS.W11.FramedArrayRewrite.config (some KS.W11.FramedArrayRewrite.program.initial)
        (denseMatrixTape (partialMatrix M (i.val * n + j.val)))
        (KS.W01.frame (KS.W01.encodeRat (schurTail (DenseRatMatrix.decode M) i j)))
        [] [] (denseMatrixCursor i j))
      (n * n * (16 * (4 * b + 3) + 31) + 16 * (4 * b + 3) + 33) := by
  exact denseMatrix_replace_time (partialMatrix M (i.val * n + j.val)) (4 * b + 3) (4 * b + 3)
    (fun k l => (partial_parts_le M b _ hnum hden k l).1)
    (fun k l => (partial_parts_le M b _ hnum hden k l).2)
    i j _ (entry_parts_le M b hnum hden i j).1 (entry_parts_le M b hnum hden i j).2

end KS.W07.SchurTable

end OAI
