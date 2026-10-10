import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorKernel

namespace OAI

/-! # The critical-line side of the compact detector contour -/

namespace Ostmann

open Complex

 theorem densityDetectorKernel_left_bound (δ u : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ‖densityDetectorKernel ((-δ : ℂ) + (u : ℂ) * I)‖ ≤
      (16 / δ) * (1 + |u|) ^ (-(3 : ℝ)) := by
  let w : ℂ := (-δ : ℂ) + (u : ℂ) * I
  have hr : w.re = -δ := by simp [w]
  have hi : w.im = u := by simp [w]
  have h0 : δ * (1 + |u|) ≤ 2 * ‖w‖ := by
    have ha := Complex.abs_re_le_norm w
    have hb := Complex.abs_im_le_norm w
    rw [hr, abs_neg, abs_of_pos hδ] at ha
    rw [hi] at hb
    nlinarith [abs_nonneg u]
  have h1 : 1 + |u| ≤ 4 * ‖w + 1‖ := by
    have ha := Complex.re_le_norm (w + 1)
    have hb := Complex.abs_im_le_norm (w + 1)
    simp only [add_re, one_re, hr, add_im, one_im, add_zero, hi] at ha hb
    linarith
  have h2 : 1 + |u| ≤ 2 * ‖w + 2‖ := by
    have ha := Complex.re_le_norm (w + 2)
    have hb := Complex.abs_im_le_norm (w + 2)
    norm_num [hr, hi] at ha hb
    linarith
  have hp : δ * (1 + |u|) ^ 3 ≤ 16 * (‖w‖ * ‖w + 1‖ * ‖w + 2‖) := by
    have h01 := mul_le_mul h0 h1 (by positivity) (by positivity)
    have h012 := mul_le_mul h01 h2 (by positivity) (by positivity)
    nlinarith
  have hn0 : 0 < ‖w‖ := by nlinarith [abs_nonneg u]
  have hn1 : 0 < ‖w + 1‖ := by linarith [abs_nonneg u]
  have hn2 : 0 < ‖w + 2‖ := by linarith [abs_nonneg u]
  change ‖1 / (w * (w + 1) * (w + 2))‖ ≤ _
  rw [norm_div, norm_one, norm_mul, norm_mul, Real.rpow_neg (by positivity : 0 ≤ 1 + |u|),
    Real.rpow_ofNat]
  rw [show (16 / δ) * ((1 + |u|) ^ 3)⁻¹ = 16 / (δ * (1 + |u|) ^ 3) by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖w‖ * ‖w + 1‖ * ‖w + 2‖)
    (by positivity : 0 < δ * (1 + |u|) ^ 3)).mpr
  nlinarith

 theorem densityDetectorKernel_high_bound (x u : ℝ) (hu : 0 < |u|) :
    ‖densityDetectorKernel ((x : ℂ) + (u : ℂ) * I)‖ ≤ (|u| ^ 3)⁻¹ := by
  let w : ℂ := (x : ℂ) + (u : ℂ) * I
  have h0 : |u| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
  have h1 : |u| ≤ ‖w + 1‖ := by simpa [w] using Complex.abs_im_le_norm (w + 1)
  have h2 : |u| ≤ ‖w + 2‖ := by simpa [w] using Complex.abs_im_le_norm (w + 2)
  have hp : |u| ^ 3 ≤ ‖w‖ * ‖w + 1‖ * ‖w + 2‖ := by
    have h01 := mul_le_mul h0 h1 hu.le (norm_nonneg _)
    have h012 := mul_le_mul h01 h2 hu.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    nlinarith
  change ‖1 / (w * (w + 1) * (w + 2))‖ ≤ _
  rw [norm_div, norm_one, norm_mul, norm_mul, ← one_div]
  exact one_div_le_one_div_of_le (pow_pos hu 3) hp

end Ostmann

end OAI
