import OAI.NumberTheory.Ostmann.ZeroDensity.DensityGaussianEnvelope

namespace OAI

/-! # The convergent vertical lines and vanishing horizontal edges -/

namespace Ostmann

open Complex Filter MeasureTheory Set
open scoped Topology Interval

noncomputable def densitySquareContour (χ : PrimitiveComplexCharacter) (s w : ℂ) : ℂ :=
  densitySquareGaussian χ s w / w

 theorem densitySquareContour_bound (χ : PrimitiveComplexCharacter) (s : ℂ) (K : ℝ)
    (hK : ∀ x u : ℝ, |x| ≤ 1 →
      ‖densitySquareGaussian χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u)
    (x u : ℝ) (hx : |x| ≤ 1) (hn : 1 ≤ ‖(x : ℂ) + u * I‖) :
    ‖densitySquareContour χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u := by
  rw [densitySquareContour, norm_div]
  exact (div_le_self (norm_nonneg _) hn).trans (hK x u hx)

 theorem densitySquareContour_vertical_integrable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (x : ℝ) (hx : |x| = 1) :
    Integrable (fun u : ℝ => densitySquareContour χ s ((x : ℂ) + u * I)) := by
  obtain ⟨K, _, hK⟩ := densitySquareGaussian_band_bound χ s hs
  have hcont : Continuous (fun u : ℝ => densitySquareContour χ s ((x : ℂ) + u * I)) := by
    have hF : Continuous (densitySquareGaussian χ s) :=
      continuous_iff_continuousAt.mpr (fun w => (densitySquareGaussian_analytic χ s w).continuousAt)
    apply (hF.comp (by fun_prop)).div (by fun_prop)
    intro u he
    have hr := congrArg Complex.re he
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      zero_mul, sub_self, add_zero, zero_re] at hr
    simp [hr] at hx
  apply (densityGaussianEnvelope_integrable.const_mul K).mono' hcont.aestronglyMeasurable
  filter_upwards with u
  apply densitySquareContour_bound χ s K hK x u hx.le
  have hn := Complex.abs_re_le_norm ((x : ℂ) + u * I)
  simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
    zero_mul, sub_self, add_zero, hx] using hn

 theorem densitySquareContour_horizontal_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (K : ℝ) (hK : ∀ x u : ℝ, |x| ≤ 1 →
      ‖densitySquareGaussian χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u)
    (u : ℝ) (hu : 1 ≤ |u|) :
    ‖∫ x in (-1 : ℝ)..1, densitySquareContour χ s ((x : ℂ) + u * I)‖ ≤
      2 * K * densityGaussianEnvelope u := by
  have hb : ∀ x ∈ Ι (-1 : ℝ) 1,
      ‖densitySquareContour χ s ((x : ℂ) + u * I)‖ ≤ K * densityGaussianEnvelope u := by
    intro x hx
    have hxm : -1 ≤ x ∧ x ≤ 1 := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      exact ⟨hx.1.le, hx.2⟩
    apply densitySquareContour_bound χ s K hK x u (abs_le.mpr hxm)
    have hn := Complex.abs_im_le_norm ((x : ℂ) + u * I)
    have he : (((x : ℂ) + u * I).im) = u := by simp
    rw [he] at hn
    exact hu.trans hn
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  norm_num at h
  convert h using 1
  ring

 theorem densitySquareContour_horizontal_tendsto (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    Tendsto (fun u : ℝ => ∫ x in (-1 : ℝ)..1,
      densitySquareContour χ s ((x : ℂ) + u * I)) atTop (𝓝 0) ∧
    Tendsto (fun u : ℝ => ∫ x in (-1 : ℝ)..1,
      densitySquareContour χ s ((x : ℂ) + (-u) * I)) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := densitySquareGaussian_band_bound χ s hs
  have he : Tendsto (fun u => 2 * K * densityGaussianEnvelope u) atTop (𝓝 0) := by
    simpa only [mul_zero] using densityGaussianEnvelope_tendsto.const_mul (2 * K)
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ he
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    exact densitySquareContour_horizontal_bound χ s K hK u (by simpa [abs_of_pos (by linarith : 0 < u)])
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ he
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have h := densitySquareContour_horizontal_bound χ s K hK (-u)
      (by simpa [abs_of_pos (by linarith : 0 < u)])
    simpa only [densityGaussianEnvelope, neg_sq, Complex.ofReal_neg] using h

end Ostmann

end OAI
