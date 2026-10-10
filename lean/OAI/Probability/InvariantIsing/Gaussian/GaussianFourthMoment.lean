import OAI.Probability.InvariantIsing.Gaussian.GaussianCoordinateNorm
import OAI.Probability.IsingPerceptron.GaussianIntegration

namespace OAI

/-! Scalar Gaussian polynomial moments needed for the quadratic leave-one-column estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma gaussianReal_pow_integrable (p : ℕ) :
    Integrable (fun x : ℝ => x^p) (gaussianReal 0 1) := by
  have hi := (IsGaussian.memLp_id (gaussianReal 0 1) p (by simp)).integrable_norm_pow'
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq,Real.norm_eq_abs,abs_pow] using hi

lemma gaussianReal_second_moment : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa only [id_eq,integral_id_gaussianReal,sub_zero,NNReal.coe_one] using h

lemma gaussianReal_fourth_moment : (∫ x : ℝ, x^4 ∂gaussianReal 0 1) = 3 := by
  have h := gaussian_integration_by_parts
    (f := fun x : ℝ => x^3) (f' := fun x => 3*x^2)
    (fun x => by simpa using hasDerivAt_pow 3 x)
    (gaussianReal_pow_integrable 3) ((gaussianReal_pow_integrable 2).const_mul 3)
    (by convert gaussianReal_pow_integrable 4 using 1; funext x; ring)
  have he : (fun x : ℝ => x*x^3) = fun x => x^4 := by funext x; ring
  rw [he,integral_const_mul,gaussianReal_second_moment,mul_one] at h
  exact h

lemma gaussianReal_square_memLp : MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using gaussianReal_pow_integrable 4

lemma gaussianReal_square_variance : variance (fun x : ℝ => x^2) (gaussianReal 0 1) = 2 := by
  rw [variance_eq_sub gaussianReal_square_memLp,gaussianReal_second_moment]
  change (∫ x : ℝ, (x^2)^2 ∂gaussianReal 0 1)-1^2 = 2
  have hp : (fun x : ℝ => (x^2)^2) = fun x => x^4 := by funext x; ring
  rw [hp,gaussianReal_fourth_moment]
  norm_num

end InvariantIsing

end

end OAI
