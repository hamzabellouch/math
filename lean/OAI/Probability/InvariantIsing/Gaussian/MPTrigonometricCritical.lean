import OAI.Probability.InvariantIsing.Gaussian.MPTrigonometricIntegral

namespace OAI

/-! The zero-edge endpoint of the MP angular integral. -/
noncomputable section
open Real MeasureTheory
namespace InvariantIsing

lemma mp_critical_sine_fraction {b : ℝ} (hb : 0 < b) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 Real.pi) :
    (sin x)^2/(b+b*cos x) = (1-cos x)/b := by
  have hc : -1 < cos x := by
    simpa only [cos_pi] using cos_lt_cos_of_nonneg_of_le_pi hx.1.le (le_refl Real.pi) hx.2
  have hd : b+b*cos x ≠ 0 := ne_of_gt (by nlinarith)
  apply (div_eq_div_iff hd hb.ne').mpr
  linear_combination b*(sin_sq_add_cos_sq x)

theorem mp_integral_sine_fraction_critical {b : ℝ} (hb : 0 < b) :
    (∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(b+b*cos x)) = Real.pi/b := by
  have he : (∫ x in (0 : ℝ)..Real.pi, (sin x)^2/(b+b*cos x)) =
      ∫ x in (0 : ℝ)..Real.pi, (1-cos x)/b := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne Real.pi] with x hx
    intro hmem
    rw [Set.uIoc_of_le pi_pos.le] at hmem
    exact mp_critical_sine_fraction hb ⟨hmem.1,lt_of_le_of_ne hmem.2 hx⟩
  rw [he,intervalIntegral.integral_div,
    intervalIntegral.integral_sub intervalIntegrable_const (continuous_cos.intervalIntegrable 0 Real.pi),
    intervalIntegral.integral_const,integral_cos]
  simp

end InvariantIsing

end

end OAI
