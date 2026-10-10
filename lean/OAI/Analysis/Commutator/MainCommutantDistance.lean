import Mathlib
import OAI.Analysis.Commutator.MainMatrix

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma diagonalAmplification_norm_le (h : ℕ) (Y : K →L[ℂ] K) :
    ‖diagonalAmplification h Y‖≤‖Y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Y)
  intro x
  have hs : ‖diagonalAmplification h Y x‖^2≤(‖Y‖*‖x‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      rw [diagonalAmplification_apply,←mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (le_opNorm Y (x i)) 2)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg Y) (norm_nonneg x))).mp hs

omit [CompleteSpace K] in
@[simp] lemma diagonalAmplification_sub (h : ℕ) (Y Z : K →L[ℂ] K) :
    diagonalAmplification h (Y-Z)=diagonalAmplification h Y-diagonalAmplification h Z := by
  ext x i
  simp

omit [CompleteSpace K] in
lemma diagonal_matrix_commute (h : ℕ) (Z : K →L[ℂ] K)
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K))
    (hZ : ∀ i j,Z*X i j=X i j*Z) :
    diagonalAmplification h Z*matrixOperator h X=matrixOperator h X*diagonalAmplification h Z := by
  ext x i
  simp only [mul_apply_eq_comp,diagonalAmplification_apply,matrixOperator_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun A : K →L[ℂ] K => A (x j)) (hZ i j)

omit [CompleteSpace K] in
lemma operator_commutator_norm_le (Y Z : K →L[ℂ] K) : ‖Y*Z-Z*Y‖≤2*‖Y‖*‖Z‖ := by
  calc
    _ ≤ ‖Y*Z‖+‖Z*Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖*‖Z‖+‖Z‖*‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

theorem matrix_commutator_bound_of_commutant_approximation
    (P : VonNeumannAlgebra K) (Y Z : K →L[ℂ] K) {c : ℝ} (hc : ‖Y-Z‖≤c)
    (hZ : ∀ a : P,Z*(a:K →L[ℂ] K)=(a:K →L[ℂ] K)*Z)
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ ≤
      2*c*‖matrixOperator h X‖ := by
  have hcomm := diagonal_matrix_commute h Z X (fun i j => hZ ⟨X i j,hX i j⟩)
  have he : diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y=
      diagonalAmplification h (Y-Z)*matrixOperator h X-matrixOperator h X*diagonalAmplification h (Y-Z) := by
    rw [diagonalAmplification_sub,sub_mul,mul_sub,hcomm]
    abel
  rw [he]
  exact (operator_commutator_norm_le _ _).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((diagonalAmplification_norm_le h (Y-Z)).trans hc) (by norm_num))
    (norm_nonneg _))

end Kadison

end

end
end

end OAI
