import OAI.Analysis.KadisonKastler.GaussianOperatorContinuity
import OAI.Analysis.KadisonKastler.GaussianStateCovariance

namespace OAI

/-! # Evaluating states on norm-continuous orbit averages

After Gaussian smoothing, a state may be interchanged with the orbit
integral even when the state is not normal. This is the bounded integration
step in Marrakchi, arXiv:1811.10253v2, Proposition 3.10.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem weightedOperatorIntegral_eq_integral
    {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (w : S → ℂ) (hw : Integrable w μ) (F : S → H →L[ℂ] H)
    (hm : AEStronglyMeasurable F μ) (C : ℝ)
    (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) :
    weightedOperatorIntegral μ w hw F
      (fun x => (ContinuousLinearMap.apply ℂ H x).continuous.comp_aestronglyMeasurable hm)
      C hb = ∫ t, w t • F t ∂μ := by
  have hi : Integrable (fun t => w t • F t) μ := by
    apply (hw.norm.mul_const C).mono' (hw.aestronglyMeasurable.smul hm)
    filter_upwards [hb] with t ht
    change ‖w t • F t‖ ≤ ‖w t‖*C
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  ext x
  exact (ContinuousLinearMap.apply ℂ H x).integral_comp_comm hi

theorem functional_weightedOperatorIntegral
    {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (w : S → ℂ) (hw : Integrable w μ) (F : S → H →L[ℂ] H)
    (hm : AEStronglyMeasurable F μ) (C : ℝ)
    (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C)
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) :
    φ (weightedOperatorIntegral μ w hw F
      (fun x => (ContinuousLinearMap.apply ℂ H x).continuous.comp_aestronglyMeasurable hm)
      C hb) = ∫ t, w t * φ (F t) ∂μ := by
  rw [weightedOperatorIntegral_eq_integral μ w hw F hm C hb]
  have hi : Integrable (fun t => w t • F t) μ := by
    apply (hw.norm.mul_const C).mono' (hw.aestronglyMeasurable.smul hm)
    filter_upwards [hb] with t ht
    change ‖w t • F t‖ ≤ ‖w t‖*C
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  rw [← φ.integral_comp_comm hi]
  simp only [map_smul,smul_eq_mul]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem invariant_functional_orbit_integral
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hφ : ∀ (t : ℝ) (a : H →L[ℂ] H), φ (stateActionOrbit U a t)=φ a)
    (μ : Measure ℝ) (w : ℝ → ℂ) (hw : Integrable w μ)
    (a : H →L[ℂ] H) (ha : Continuous (stateActionOrbit U a)) :
    φ (weightedOperatorIntegral μ w hw (stateActionOrbit U a)
      (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
      ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)) =
        (∫ t, w t ∂μ)*φ a := by
  rw [functional_weightedOperatorIntegral μ w hw (stateActionOrbit U a)
    ha.aestronglyMeasurable ‖a‖ _ φ]
  simp_rw [hφ]
  exact integral_mul_const _ _

theorem gaussianStateAverage_orbit_continuous
    (a : H →L[ℂ] H) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Continuous (fun t : ℝ =>
      stateActionOrbit U (gaussianStateAverage U hU a r hr z) t) := by
  have he (t : ℝ) :
      stateActionOrbit U (gaussianStateAverage U hU a r hr z) t =
        gaussianStateAverage U hU a r hr (z+t) :=
    gaussianStateAverage_covariance U hU a r hr z t
  simp_rw [he]
  exact (gaussianStateAverage_continuous U hU a hr).comp
    (continuous_const.add Complex.continuous_ofReal)

end

end KadisonKastler

end OAI
