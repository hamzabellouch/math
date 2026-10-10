import OAI.Probability.InvariantIsing.Fields.FieldGaussianTransformLaw
import OAI.Probability.InvariantIsing.Fields.FieldSpinLinear
import Mathlib.MeasureTheory.Group.IntegralConvolution

namespace OAI

/-! Combining successive Gaussian increments with the same exponent.
Both the log partition and the normalized transition retain their actual
Gaussian laws, including zero variances and the ordinary exponent zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal

namespace InvariantIsing

lemma fieldGaussian_integral_comp (v w : ℝ≥0) (z : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hi : Integrable f (gaussianReal z (v + w))) :
    (∫ x, (∫ y, f y ∂gaussianReal x w) ∂gaussianReal z v) =
      ∫ y, f y ∂gaussianReal z (v + w) := by
  have hc : (gaussianReal z v) ∗ (gaussianReal 0 w) = gaussianReal z (v + w) := by
    simpa only [add_zero] using gaussianReal_conv_gaussianReal (m₁ := z) (m₂ := 0)
      (v₁ := v) (v₂ := w)
  have hi' : Integrable f ((gaussianReal z v) ∗ (gaussianReal 0 w)) := by rwa [hc]
  simp_rw [field_gaussian_integral_shift w _ hf]
  simpa only [hc] using (integral_conv hi').symm

lemma exp_mul_gaussianOperator (ζ : ℝ) (w : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (z : ℝ) :
    Real.exp (ζ * gaussianOperator ζ w F z) =
      ∫ y, Real.exp (ζ * F y) ∂gaussianReal z w := by
  by_cases hζ : ζ = 0
  · subst ζ
    simp only [zero_mul, Real.exp_zero, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul]
  · have hp : 0 < ∫ y, Real.exp (ζ * F y) ∂gaussianReal z w :=
      MeasureTheory.integral_exp_pos (integrable_exp_of_linearGrowth _
        (gaussianReal_exponentialNormMoments z w) hF hG ζ)
    rw [gaussianOperator_eq_gaussian_exp_integral hζ w hF z]
    rw [← mul_assoc, mul_inv_cancel₀ hζ, one_mul, Real.exp_log hp]

theorem gaussianOperator_same_exponent (ζ : ℝ) (v w : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (z : ℝ) :
    gaussianOperator ζ v (gaussianOperator ζ w F) z =
      gaussianOperator ζ (v + w : ℝ≥0) F z := by
  have hm : Measurable (gaussianOperator ζ w F) := by
    rw [gaussianOperator_eq_transform]
    exact measurable_gaussianTransform hF w ζ
  by_cases hζ : ζ = 0
  · subst ζ
    rw [gaussianOperator_eq_gaussian_integral v hm z,
      gaussianOperator_eq_gaussian_integral (v + w) hF z]
    simp_rw [gaussianOperator_eq_gaussian_integral w hF]
    exact fieldGaussian_integral_comp v w z hF (field_gaussian_linear_integrable (v + w) z hF hG)
  · rw [gaussianOperator_eq_gaussian_exp_integral hζ v hm z,
      gaussianOperator_eq_gaussian_exp_integral hζ (v + w) hF z]
    apply congrArg (fun r : ℝ => ζ⁻¹ * Real.log r)
    simp_rw [exp_mul_gaussianOperator ζ w hF hG]
    exact fieldGaussian_integral_comp v w z (hF.const_mul ζ).exp
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z (v + w)) hF hG ζ)

theorem fieldSpinTransition_same_exponent (ζ : ℝ) (v w : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a)
    {B : ℝ} (haB : ∀ y, |a y| ≤ B) (z : ℝ) :
    fieldSpinTransition ζ v (gaussianOperator ζ w F) (fieldSpinTransition ζ w F a) z =
      fieldSpinTransition ζ (v + w) F a z := by
  have hE (x : ℝ) (u : ℝ≥0) :
      Integrable (fun y => Real.exp (ζ * F y)) (gaussianReal x u) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments x u) hF hG ζ
  have hN : Integrable (fun y => Real.exp (ζ * F y) * a y)
      (gaussianReal z (v + w)) := by
    refine ((hE z (v + w)).mul_const B).mono'
      (((hF.const_mul ζ).exp.mul ha).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (haB y) (Real.exp_pos _).le
  have hn : (∫ x, Real.exp (ζ * gaussianOperator ζ w F x) *
      fieldSpinTransition ζ w F a x ∂gaussianReal z v) =
      ∫ y, Real.exp (ζ * F y) * a y ∂gaussianReal z (v + w) := by
    calc
      _ = ∫ x, (∫ y, Real.exp (ζ * F y) * a y ∂gaussianReal x w) ∂gaussianReal z v := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [exp_mul_gaussianOperator ζ w hF hG x, fieldSpinTransition,
          integral_tilted_eq_div]
        have hp := (MeasureTheory.integral_exp_pos (hE x w)).ne'
        exact mul_div_cancel₀ _ hp
      _ = _ := fieldGaussian_integral_comp v w z ((hF.const_mul ζ).exp.mul ha) hN
  have hd : (∫ x, Real.exp (ζ * gaussianOperator ζ w F x) ∂gaussianReal z v) =
      ∫ y, Real.exp (ζ * F y) ∂gaussianReal z (v + w) := by
    simp_rw [exp_mul_gaussianOperator ζ w hF hG]
    exact fieldGaussian_integral_comp v w z (hF.const_mul ζ).exp (hE z (v + w))
  calc
    _ = (∫ x, Real.exp (ζ * gaussianOperator ζ w F x) *
          fieldSpinTransition ζ w F a x ∂gaussianReal z v) /
        (∫ x, Real.exp (ζ * gaussianOperator ζ w F x) ∂gaussianReal z v) :=
      integral_tilted_eq_div _ _ _
    _ = _ := by rw [hn, hd, fieldSpinTransition, integral_tilted_eq_div]

end InvariantIsing

end

end OAI
