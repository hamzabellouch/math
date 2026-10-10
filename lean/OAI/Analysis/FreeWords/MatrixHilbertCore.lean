import Mathlib
import OAI.Analysis.FreeWords.MatrixHilbertDefinitions

namespace OAI

noncomputable section

namespace KKMatrixHilbert

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {n:ℕ}

omit [CompleteSpace H] in
theorem matrixOperator_add (a b:Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    matrixOperator (a+b)=matrixOperator a+matrixOperator b := by
  ext x i
  simp [matrixOperator_apply,Matrix.add_apply,Finset.sum_add_distrib]

omit [CompleteSpace H] in
theorem matrixOperator_mul (a b:Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    matrixOperator (a*b)=matrixOperator a*matrixOperator b := by
  ext x i
  simp only [matrixOperator_apply,Matrix.mul_apply,sum_apply,
    mul_apply_eq_comp,map_sum]
  rw [Finset.sum_comm]

omit [CompleteSpace H] in
theorem matrixOperator_one : matrixOperator (1:Matrix (Fin n) (Fin n) (H →L[ℂ] H))=1 := by
  ext x i
  simp only [matrixOperator_apply,Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Ne.symm hji]
  · simp

theorem matrixOperator_star (a:Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    matrixOperator (star a)=star (matrixOperator a) := by
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply,matrixOperator_apply,Matrix.star_apply,sum_inner,inner_sum,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

def matrixOperatorHom : Matrix (Fin n) (Fin n) (H →L[ℂ] H) →⋆ₐ[ℂ]
    (Amplification n H →L[ℂ] Amplification n H) where
  toFun := matrixOperator
  map_zero' := by ext x i; simp
  map_one' := matrixOperator_one
  map_add' := matrixOperator_add
  map_mul' := matrixOperator_mul
  commutes' c := by
    ext x i
    simp only [matrixOperator_apply,Matrix.algebraMap_eq_diagonal,Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Ne.symm hji]
    · simp
  map_star' := matrixOperator_star

omit [CompleteSpace H] in
theorem matrixOperator_diagonal_apply (h:H →L[ℂ] H) (x:Amplification n H) (i:Fin n) :
    matrixOperator (Matrix.diagonal fun _:Fin n => h) x i=h (x i) := by
  simp only [matrixOperator_apply,Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Ne.symm hji]
  · simp

omit [CompleteSpace H] in
theorem norm_diagonal_le (h:H →L[ℂ] H) :
    ‖matrixOperator (Matrix.diagonal fun _:Fin n => h)‖≤‖h‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [matrixOperator_diagonal_apply]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (h.le_opNorm (x i)) 2

end

end KKMatrixHilbert
end

end OAI
