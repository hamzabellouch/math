import Mathlib
import OAI.RepresentationTheory.PartialPermutation.HilbertSchmidt

namespace OAI

namespace PartialPermutation
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]

lemma norm_apply_sq_le_hsNormSq (A : Module.End ℂ V) (x : V) :
    ‖A x‖^2 ≤ hsNormSq A * ‖x‖^2 := by
  let e := stdOrthonormalBasis ℂ V
  calc
    ‖A x‖^2 = ∑ i, ‖inner ℂ (e i) (A x)‖^2 := (e.sum_sq_norm_inner_right _).symm
    _ ≤ ∑ i, ‖LinearMap.adjoint A (e i)‖^2 * ‖x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [← LinearMap.adjoint_inner_left A]
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (inner ℂ (LinearMap.adjoint A (e i)) x))
        (norm_inner_le_norm (𝕜 := ℂ) (LinearMap.adjoint A (e i)) x) 2
    _ = hsNormSq A * ‖x‖^2 := by
      rw [← Finset.sum_mul, ← hsNormSq_eq_sum e, hsNormSq_adjoint]

lemma opNorm_sq_le_hsNormSq (A : Module.End ℂ V) :
    ‖LinearMap.toContinuousLinearMap A‖^2 ≤ hsNormSq A := by
  have h : ‖LinearMap.toContinuousLinearMap A‖ ≤ Real.sqrt (hsNormSq A) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (hsNormSq_nonneg A)]
    exact norm_apply_sq_le_hsNormSq A x
  simpa only [Real.sq_sqrt (hsNormSq_nonneg A)] using
    pow_le_pow_left₀ (norm_nonneg _) h 2

end
end PartialPermutation

end OAI
