import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogWindow
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFourierCauchy

namespace OAI

/-! The logarithmic-window multiplier has square-integrable quadratic
decay. These bounds keep the actual finite window width. -/

namespace TwoPointCorrelations

open Complex MeasureTheory FourierTransform

lemma mrtWindowMultiplier_continuous (a : ℝ) : Continuous (mrtWindowMultiplier a) := by
  unfold mrtWindowMultiplier
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact mrt_one_add_imaginary_ne_zero

lemma mrt_window_multiplier_sq (a t : ℝ) :
    ‖mrtWindowMultiplier a t‖ ^ 2 ≤ (Real.exp a + 1) ^ 2 / (1 + t ^ 2) := by
  have hn : ‖Complex.exp (((1 : ℂ) + (t : ℂ) * I) * a) - 1‖ ≤ Real.exp a + 1 := by
    apply (norm_sub_le _ _).trans
    simp [Complex.norm_exp, mul_re]
  have hd : ‖(1 : ℂ) + (t : ℂ) * I‖ ^ 2 = 1 + t ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  unfold mrtWindowMultiplier
  rw [norm_div, div_pow, hd]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity)

lemma mrt_log_window_atom_fourier_norm (b : ℝ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    ‖𝓕 (mrtLogWindowAtom b a) t‖ ^ 2 =
      Real.exp (-b) ^ 2 * ‖mrtWindowMultiplier a (2 * Real.pi * t)‖ ^ 2 := by
  rw [mrt_log_window_fourier b ha, norm_mul, mul_pow]
  congr 1
  rw [Complex.norm_exp]
  congr 2
  simp

lemma mrt_log_window_atom_fourier_memLp (b : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    MemLp (𝓕 (mrtLogWindowAtom b a)) 2 := by
  have hc : Continuous (𝓕 (mrtLogWindowAtom b a)) := by
    convert (Continuous.mul
      (show Continuous (fun t : ℝ =>
        Complex.exp (-((1 : ℂ) + (2 * Real.pi * t : ℝ) * I) * b)) by fun_prop)
      ((mrtWindowMultiplier_continuous a).comp (by fun_prop :
        Continuous (fun t : ℝ => 2 * Real.pi * t)))) using 1
    ext t
    exact mrt_log_window_fourier b ha t
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hm := (integrable_inv_one_add_mul_sq
    (show (2 : ℝ) * Real.pi ≠ 0 by positivity)).const_mul
      (Real.exp (-b) ^ 2 * (Real.exp a + 1) ^ 2)
  apply hm.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards with t
  simp only [Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mrt_log_window_atom_fourier_norm b ha]
  have hh := mul_le_mul_of_nonneg_left (mrt_window_multiplier_sq a (2 * Real.pi * t))
    (sq_nonneg (Real.exp (-b)))
  convert hh using 1
  ring

end TwoPointCorrelations

end OAI
