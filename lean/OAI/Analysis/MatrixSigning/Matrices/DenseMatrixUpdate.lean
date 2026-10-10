import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.DenseMatrixSerialization

namespace OAI

namespace KS.W08

open KS.W07

def denseMatrixSet {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) (q : ℚ) : DenseRatMatrix n :=
  M.set i.val ((M.get i).set j.val q j.isLt) i.isLt

theorem denseMatrixSet_decode {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) (q : ℚ)
    (k l : Fin n) : DenseRatMatrix.decode (denseMatrixSet M i j q) k l =
      if i = k ∧ j = l then q else DenseRatMatrix.decode M k l := by
  change (M.set i.val (M[i.val].set j.val q j.isLt) i.isLt)[k.val][l.val] =
    if i = k ∧ j = l then q else M[k.val][l.val]
  by_cases hi : i.val = k.val <;> by_cases hj : j.val = l.val <;>
    simp [Fin.ext_iff, hi, hj]

theorem denseMatrixPayloads_get_fin {n : ℕ} (M : DenseRatMatrix n) (k : Fin (n * n)) :
    (denseMatrixPayloads M)[k.val]'(by rw [denseMatrixPayloads_length]; exact k.isLt) =
      KS.W01.encodeRat (DenseRatMatrix.decode M (finProdFinEquiv.symm k).1
        (finProdFinEquiv.symm k).2) := by
  unfold denseMatrixPayloads
  rw [List.getElem_ofFn]

theorem matrixEntryIndex_eq_iff {n : ℕ} (i j : Fin n) (k : Fin (n * n)) :
    (i = (finProdFinEquiv.symm k).1 ∧ j = (finProdFinEquiv.symm k).2) ↔
      i.val * n + j.val = k.val := by
  constructor
  · rintro ⟨hi, hj⟩
    have hp : (i, j) = finProdFinEquiv.symm k := Prod.ext hi hj
    have he := congrArg finProdFinEquiv hp
    rw [Equiv.apply_symm_apply] at he
    have hv := congrArg Fin.val he
    change (matrixEntryIndex i j).val = k.val at hv
    simpa only [matrixEntryIndex_val] using hv
  · intro h
    have he : matrixEntryIndex i j = k := Fin.ext (by simpa using h)
    have hp := congrArg finProdFinEquiv.symm he
    change finProdFinEquiv.symm (finProdFinEquiv (i, j)) = finProdFinEquiv.symm k at hp
    rw [Equiv.symm_apply_apply] at hp
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

theorem denseMatrixPayloads_set {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) (q : ℚ) :
    denseMatrixPayloads (denseMatrixSet M i j q) =
      (denseMatrixPayloads M).set (i.val * n + j.val) (KS.W01.encodeRat q) := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hkn : k < n * n := by simpa using hk
    let f : Fin (n * n) := ⟨k, hkn⟩
    rw [List.getElem_set]
    change (denseMatrixPayloads (denseMatrixSet M i j q))[f.val] =
      if i.val * n + j.val = f.val then KS.W01.encodeRat q else (denseMatrixPayloads M)[f.val]
    rw [denseMatrixPayloads_get_fin, denseMatrixPayloads_get_fin, denseMatrixSet_decode]
    simp only [matrixEntryIndex_eq_iff, apply_ite]
    split <;> simp_all

theorem denseMatrixTape_set {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) (q : ℚ) :
    denseMatrixTape (denseMatrixSet M i j q) =
      ((denseMatrixPayloads M).set (i.val * n + j.val) (KS.W01.encodeRat q)).flatMap KS.W01.frame := by
  rw [denseMatrixTape, denseMatrixPayloads_set]

end KS.W08

end OAI
