import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Model

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate

namespace PartialPermutation
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]

lemma hsNormSq_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ V)
    (A : Module.End ℂ V) : hsNormSq A = ∑ i, ‖A (e i)‖ ^ 2 := by
  rw [hsNormSq, LinearMap.trace_eq_sum_inner _ e, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, LinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (A (e i))

lemma hsNormSq_nonneg (A : Module.End ℂ V) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum (stdOrthonormalBasis ℂ V)]
  positivity

open scoped Matrix.Norms.Frobenius in

lemma hsNormSq_eq_matrix_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℂ V) (A : Module.End ℂ V) :
    hsNormSq A = ‖LinearMap.toMatrix e.toBasis e.toBasis A‖ ^ 2 := by
  rw [hsNormSq_eq_sum e, Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_sq_norm_inner_right (A (e i))]
  apply Finset.sum_congr rfl
  intro j _
  simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply, e.coe_toBasis_repr_apply]

lemma hsNormSq_adjoint (A : Module.End ℂ V) : hsNormSq (LinearMap.adjoint A) = hsNormSq A := by
  unfold hsNormSq
  rw [LinearMap.adjoint_adjoint, LinearMap.trace_mul_comm]

lemma hsNormSq_projection_left (W : Submodule ℂ V) (A : Module.End ℂ V) :
    hsNormSq (W.starProjection.toLinearMap * A) ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum (stdOrthonormalBasis ℂ V), hsNormSq_eq_sum (stdOrthonormalBasis ℂ V)]
  exact Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (W.norm_starProjection_apply_le _) 2

lemma adjoint_mul_eq (A B : Module.End ℂ V) :
    LinearMap.adjoint (A * B) = LinearMap.adjoint B * LinearMap.adjoint A :=
  LinearMap.adjoint_comp A B

lemma adjoint_projection_eq (W : Submodule ℂ V) :
    LinearMap.adjoint W.starProjection.toLinearMap = W.starProjection.toLinearMap := by
  ext v
  apply ext_inner_left ℂ
  intro u
  rw [LinearMap.adjoint_inner_right]
  exact W.inner_starProjection_left_eq_right u v

lemma hsNormSq_projection_right (W : Submodule ℂ V) (A : Module.End ℂ V) :
    hsNormSq (A * W.starProjection.toLinearMap) ≤ hsNormSq A := by
  rw [← hsNormSq_adjoint (A * _), adjoint_mul_eq, adjoint_projection_eq,
    ← hsNormSq_adjoint A]
  exact hsNormSq_projection_left W _

open scoped Matrix.Norms.Frobenius in

lemma hsNormSq_mul_le (A B : Module.End ℂ V) :
    hsNormSq (A * B) ≤ hsNormSq A * hsNormSq B := by
  let e := stdOrthonormalBasis ℂ V
  rw [hsNormSq_eq_matrix_norm_sq e, hsNormSq_eq_matrix_norm_sq e,
    hsNormSq_eq_matrix_norm_sq e, LinearMap.toMatrix_mul]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (Matrix.frobenius_norm_mul (LinearMap.toMatrix e.toBasis e.toBasis A)
      (LinearMap.toMatrix e.toBasis e.toBasis B)) 2

open scoped Matrix.Norms.Frobenius in

lemma hsNormSq_sum_le {ι : Type*} [Fintype ι] (A : ι → Module.End ℂ V) :
    hsNormSq (∑ i, A i) ≤ (Fintype.card ι : ℝ) * ∑ i, hsNormSq (A i) := by
  classical
  let e := stdOrthonormalBasis ℂ V
  simp_rw [hsNormSq_eq_matrix_norm_sq e]
  rw [map_sum]
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
    (f := fun _ : ι => (1 : ℝ))
    (g := fun i => ‖LinearMap.toMatrix e.toBasis e.toBasis (A i)‖ ^ 2)
    (r := fun i => ‖LinearMap.toMatrix e.toBasis e.toBasis (A i)‖)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  simpa using h

end
end PartialPermutation

end

end OAI
