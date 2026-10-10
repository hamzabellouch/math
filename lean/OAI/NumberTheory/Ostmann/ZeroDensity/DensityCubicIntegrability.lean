import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPackedCharacterMoments
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityWeightedProductCauchy

namespace OAI

/-! # Integrability of the mixed critical-line detector product -/

namespace Ostmann

open MeasureTheory

 theorem densityCubicWeight_continuous : Continuous densityCubicWeight := by
  unfold densityCubicWeight
  exact continuous_const.div ((continuous_const.add continuous_abs).pow 3) (fun _ => by positivity)

 theorem densityCubicWeight_integrable : Integrable densityCubicWeight := by
  have h : Integrable (fun v : ℝ => (1 + ‖v‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 3)
  simpa only [Real.norm_eq_abs, ← densityCubicWeight_rpow] using h

 theorem densityCubicWeight_shift_integrable (t : ℝ) :
    Integrable (fun v => densityCubicWeight (v - t)) :=
  densityCubicWeight_integrable.comp_sub_right t

 theorem densityCubicWeight_shift_integral (t : ℝ) :
    (∫ v, densityCubicWeight (v - t)) = ∫ v, densityCubicWeight v :=
  integral_sub_right_eq_self densityCubicWeight t

 theorem density_cubic_mixed_integrable (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ v, 0 ≤ f v) (hg0 : ∀ v, 0 ≤ g v) (t : ℝ)
    (h4 : Integrable (fun v => densityCubicWeight (v - t) * f v ^ 4))
    (h2g : Integrable (fun v => densityCubicWeight (v - t) * g v ^ 2)) :
    Integrable (fun v => densityCubicWeight (v - t) * f v ^ 2) ∧
    Integrable (fun v => densityCubicWeight (v - t) * f v * g v) := by
  have hwc : Continuous (fun v => densityCubicWeight (v - t)) :=
    densityCubicWeight_continuous.comp (continuous_id.sub continuous_const)
  have h2 : Integrable (fun v => densityCubicWeight (v - t) * f v ^ 2) := by
    apply ((densityCubicWeight_shift_integrable t).add h4).mono'
      (hwc.mul (hf.pow 2)).aestronglyMeasurable
    filter_upwards with v
    change ‖densityCubicWeight (v - t) * f v ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityCubicWeight_nonneg _) (sq_nonneg _))]
    have h : f v ^ 2 ≤ 1 + f v ^ 4 := by nlinarith [sq_nonneg (f v ^ 2 - 1)]
    have hh := mul_le_mul_of_nonneg_left h (densityCubicWeight_nonneg (v - t))
    simpa only [mul_add, mul_one, Pi.add_apply] using hh
  refine ⟨h2, ?_⟩
  apply (h2.add h2g).mono' ((hwc.mul hf).mul hg).aestronglyMeasurable
  filter_upwards with v
  change ‖densityCubicWeight (v - t) * f v * g v‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (densityCubicWeight_nonneg _) (hf0 v)) (hg0 v))]
  have h : f v * g v ≤ f v ^ 2 + g v ^ 2 := by nlinarith [sq_nonneg (f v - g v)]
  have hh := mul_le_mul_of_nonneg_left h (densityCubicWeight_nonneg (v - t))
  simpa only [mul_add, mul_assoc, Pi.add_apply] using hh

end Ostmann

end OAI
