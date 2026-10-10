import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticEncodingSize
import OAI.Analysis.MatrixSigning.Matrices.DenseRatMatrix

namespace OAI

section

namespace KS.W08

open KS.W07
open scoped BigOperators

def matrixEntryIndex {n : ℕ} (i j : Fin n) : Fin (n * n) := finProdFinEquiv (i, j)

@[simp] theorem matrixEntryIndex_val {n : ℕ} (i j : Fin n) :
    (matrixEntryIndex i j).val = i.val * n + j.val := by
  simp [matrixEntryIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem matrixEntryIndex_lt {n : ℕ} (i j : Fin n) : i.val * n + j.val < n * n := by
  simpa using (matrixEntryIndex i j).isLt

def denseMatrixPayloads {n : ℕ} (M : DenseRatMatrix n) : List (List Bool) :=
  List.ofFn (fun k : Fin (n * n) =>
    KS.W01.encodeRat (DenseRatMatrix.decode M (finProdFinEquiv.symm k).1
      (finProdFinEquiv.symm k).2))

@[simp] theorem denseMatrixPayloads_length {n : ℕ} (M : DenseRatMatrix n) :
    (denseMatrixPayloads M).length = n * n := by simp [denseMatrixPayloads]

theorem denseMatrixPayloads_get {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (denseMatrixPayloads M)[i.val * n + j.val]'(by
      rw [denseMatrixPayloads_length]
      exact matrixEntryIndex_lt i j) = KS.W01.encodeRat (DenseRatMatrix.decode M i j) := by
  have h : (denseMatrixPayloads M)[(matrixEntryIndex i j).val]'(by
      rw [denseMatrixPayloads_length]
      exact (matrixEntryIndex i j).isLt) =
      KS.W01.encodeRat (DenseRatMatrix.decode M i j) := by
    unfold denseMatrixPayloads
    rw [List.getElem_ofFn]
    change KS.W01.encodeRat (DenseRatMatrix.decode M
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = _
    simp only [Equiv.symm_apply_apply]
  simpa only [matrixEntryIndex_val] using h

def denseMatrixTape {n : ℕ} (M : DenseRatMatrix n) : List Bool :=
  (denseMatrixPayloads M).flatMap KS.W01.frame

def denseMatrixCursor {n : ℕ} (i j : Fin n) : List Bool :=
  List.replicate (i.val * n + j.val) true

@[simp] theorem denseMatrixCursor_length {n : ℕ} (i j : Fin n) :
    (denseMatrixCursor i j).length = i.val * n + j.val := by simp [denseMatrixCursor]

theorem denseMatrixTape_length {n : ℕ} (M : DenseRatMatrix n) :
    (denseMatrixTape M).length = ∑ k : Fin (n * n),
      (2 * (KS.W01.encodeRat (DenseRatMatrix.decode M (finProdFinEquiv.symm k).1
        (finProdFinEquiv.symm k).2)).length + 1) := by
  simp [denseMatrixTape, denseMatrixPayloads, List.length_flatMap,
    List.sum_ofFn, KS.W01.length_frame]

theorem denseMatrixTape_length_le {n : ℕ} (M : DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) :
    (denseMatrixTape M).length ≤ n * n * (8 * b + 15) := by
  rw [denseMatrixTape_length]
  calc
    _ ≤ ∑ _k : Fin (n * n), (8 * b + 15) := by
      apply Finset.sum_le_sum
      intro k _
      have h := KS.W01.ratLength_le_of_parts
        (DenseRatMatrix.decode M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
        b b (hnum _ _) (hden _ _)
      unfold KS.W01.ratLength at h
      omega
    _ = _ := by simp [Nat.mul_comm]

theorem denseMatrixScanSize_le {n : ℕ} (M : DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2 ^ b) (i j : Fin n) :
    (denseMatrixTape M).length + (denseMatrixCursor i j).length + 1 ≤
      n * n * (8 * b + 16) + 1 := by
  have ht := denseMatrixTape_length_le M b hnum hden
  have hi := (matrixEntryIndex_lt i j).le
  rw [denseMatrixCursor_length]
  calc
    _ ≤ n * n * (8 * b + 15) + n * n + 1 := Nat.add_le_add_right (Nat.add_le_add ht hi) 1
    _ = _ := by ring

end KS.W08

end

end OAI
