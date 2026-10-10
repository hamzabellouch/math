import OAI.Analysis.FreeEntropy.FreeMatrixModels

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
 def matrixBlocks {d p : ℕ} : (Fin p → Matrix (Fin d) (Fin d) ℂ) →+* Matrix (Fin (d*p)) (Fin (d*p)) ℂ :=
  (Matrix.reindexRingEquiv ℂ finProdFinEquiv).toRingHom.comp (Matrix.blockDiagonalRingHom (Fin d) (Fin p) ℂ)
 theorem matrixBlocks_apply {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) (l r : Fin p) :
    matrixBlocks A (finProdFinEquiv (j,l)) (finProdFinEquiv (k,r)) = if l=r then A l j k else 0 := by
  change Matrix.blockDiagonal A (finProdFinEquiv.symm (finProdFinEquiv (j,l))) (finProdFinEquiv.symm (finProdFinEquiv (k,r))) = _
  simp only [Equiv.symm_apply_apply,Matrix.blockDiagonal]
  rfl
 theorem trace_matrixBlocks {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (matrixBlocks A) = ∑ l, Matrix.trace (A l) := by
  rw [Matrix.trace]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type,Matrix.diag,matrixBlocks_apply,ite_true]
  rw [Finset.sum_comm]
  rfl
 def blockVector {d p : ℕ} (v : EuclideanSpace ℂ (Fin (d*p))) (l : Fin p) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun j => v (finProdFinEquiv (j,l)))
 theorem blockVector_normSq {d p : ℕ} (v : EuclideanSpace ℂ (Fin (d*p))) :
    ∑ l : Fin p, ‖blockVector v l‖^2 = ‖v‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,blockVector]
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
 theorem matrixBlocks_mulVec {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin (d*p))) (l : Fin p) :
    blockVector (matrixOperator (matrixBlocks A) v) l = matrixOperator (A l) (blockVector v l) := by
  ext j
  change (matrixBlocks A).mulVec v.ofLp (finProdFinEquiv (j,l)) = (A l).mulVec (fun k => v (finProdFinEquiv (k,l))) j
  simp only [Matrix.mulVec,dotProduct]
  rw [← finProdFinEquiv.sum_comp]
  simp [Fintype.sum_prod_type,matrixBlocks_apply]
 theorem matrixBlocks_norm_le {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    {K : ℝ} (hK : 0≤K) (hA : ∀ l, matrixOpNorm (A l)≤K) : matrixOpNorm (matrixBlocks A)≤K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  have he : ‖matrixOperator (matrixBlocks A) v‖^2 ≤ K^2*‖v‖^2 := by
    rw [← blockVector_normSq,← blockVector_normSq v,Finset.mul_sum]
    apply sum_le_sum
    intro l _
    rw [matrixBlocks_mulVec,← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((matrixOperator (A l)).le_opNorm (blockVector v l) |>.trans (mul_le_mul_of_nonneg_right (hA l) (norm_nonneg _))) 2
  change ‖matrixOperator (matrixBlocks A) v‖ ≤ K*‖v‖
  nlinarith [norm_nonneg (matrixOperator (matrixBlocks A) v),mul_nonneg hK (norm_nonneg v)]
 theorem matrixBlocks_isHermitian {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ l,(A l).IsHermitian) : (matrixBlocks A).IsHermitian := by
  ext j k
  obtain ⟨⟨j,l⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨k,r⟩,rfl⟩ := finProdFinEquiv.surjective k
  simp only [Matrix.conjTranspose_apply,matrixBlocks_apply]
  by_cases h:l=r
  · subst r; simp only [ite_true]; exact congrFun (congrFun (hA l) j) k
  · simp [h,Ne.symm h]
end FiniteEntropySeparation

end

end OAI
