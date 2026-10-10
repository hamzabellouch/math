import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorWeight

namespace OAI

/-! # The cubic vertical decay of the compact zero-detector kernel -/

namespace Ostmann

open Complex MeasureTheory

 theorem densityDetectorKernel_line_bound (σ t : ℝ) (hσ : 1 ≤ σ) :
    ‖densityDetectorKernel ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      8 * (1 + |t|) ^ (-(3 : ℝ)) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hr : s.re = σ := by simp [s]
  have hi : s.im = t := by simp [s]
  have h0 : 1 + |t| ≤ 2 * ‖s‖ := by
    have ha := Complex.re_le_norm s
    have hb := Complex.abs_im_le_norm s
    rw [hr] at ha
    rw [hi] at hb
    linarith
  have h1 : 1 + |t| ≤ 2 * ‖s + 1‖ := by
    have ha := Complex.re_le_norm (s + 1)
    have hb := Complex.abs_im_le_norm (s + 1)
    simp only [add_re, one_re, hr, add_im, one_im, add_zero, hi] at ha hb
    linarith
  have h2 : 1 + |t| ≤ 2 * ‖s + 2‖ := by
    have ha := Complex.re_le_norm (s + 2)
    have hb := Complex.abs_im_le_norm (s + 2)
    norm_num [hr, hi] at ha hb
    linarith
  have hp : (1 + |t|) ^ 3 ≤ 8 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖) := by
    have h01 := mul_le_mul h0 h1 (by positivity) (by positivity)
    have h012 := mul_le_mul h01 h2 (by positivity) (by positivity)
    nlinarith
  have hn0 : 0 < ‖s‖ := by linarith [abs_nonneg t]
  have hn1 : 0 < ‖s + 1‖ := by linarith [abs_nonneg t]
  have hn2 : 0 < ‖s + 2‖ := by linarith [abs_nonneg t]
  change ‖1 / (s * (s + 1) * (s + 2))‖ ≤ _
  rw [norm_div, norm_one, norm_mul, norm_mul, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|),
    Real.rpow_ofNat, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
    (by positivity : 0 < (1 + |t|) ^ 3)).mpr
  nlinarith

 theorem densityDetectorKernel_verticalIntegrable (σ : ℝ) (hσ : 1 ≤ σ) :
    Complex.VerticalIntegrable densityDetectorKernel σ := by
  have hmajor : Integrable (fun t : ℝ => 8 * (1 + ‖t‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 3)).const_mul 8
  have hc : Continuous (fun t : ℝ => densityDetectorKernel ((σ : ℂ) + (t : ℂ) * I)) := by
    unfold densityDetectorKernel
    apply continuous_const.div
    · fun_prop
    · intro t
      apply mul_ne_zero
      · apply mul_ne_zero
        · intro h
          have hr := congrArg Complex.re h
          simp at hr
          linarith
        · intro h
          have hr := congrArg Complex.re h
          simp at hr
          linarith
      · intro h
        have hr := congrArg Complex.re h
        simp at hr
        linarith
  apply hmajor.mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs] using densityDetectorKernel_line_bound σ t hσ

 theorem densityDetectorWeight_mellin_inversion (σ x : ℝ) (hσ : 1 ≤ σ) (hx : 0 < x) :
    mellinInv σ densityDetectorKernel x = densityDetectorWeight x := by
  have hσp : 0 < σ := by linarith
  have hF : Complex.VerticalIntegrable (mellin densityDetectorWeight) σ := by
    have he : (fun t : ℝ => mellin densityDetectorWeight ((σ : ℂ) + (t : ℂ) * I)) =
        (fun t : ℝ => densityDetectorKernel ((σ : ℂ) + (t : ℂ) * I)) := by
      funext t
      exact (densityDetectorWeight_hasMellin _ (by simpa using hσp)).2
    change Integrable (fun t : ℝ => mellin densityDetectorWeight ((σ : ℂ) + (t : ℂ) * I))
    rw [he]
    exact densityDetectorKernel_verticalIntegrable σ hσ
  have hi := mellinInv_mellin_eq σ densityDetectorWeight hx
    (densityDetectorWeight_hasMellin (σ : ℂ) hσp).1 hF densityDetectorWeight_continuous.continuousAt
  rw [← hi]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [(densityDetectorWeight_hasMellin ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσp)).2]

end Ostmann

end OAI
