import OAI.NumberTheory.Ostmann.ZeroDensity.SharpGammaHorizontal

namespace OAI

/-! # Bounded vertical logarithmic variation of Gamma -/

namespace Ostmann

open Complex Set

 theorem sharp_gamma_log_vertical_ordered (a u v : ℝ)
    (ha : 1 / 8 ≤ a) (ha3 : a ≤ 3) (huv : u ≤ v) :
    |Real.log ‖Complex.Gamma ((a : ℂ) + v * I)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + u * I)‖| ≤
      (59 + |Real.eulerMascheroniConstant|) * (v - u) := by
  let F : ℝ → ℝ := fun y => Real.log ‖Complex.Gamma ((a : ℂ) + y * I)‖
  let F' : ℝ → ℝ := fun y => -(Complex.digamma ((a : ℂ) + y * I)).im
  have hd (y : ℝ) : HasDerivAt F (F' y) y :=
    gamma_log_norm_vertical a y (by linarith)
  have hb (y : ℝ) : ‖F' y‖ ≤ 59 + |Real.eulerMascheroniConstant| := by
    have h := sharp_digamma_strip ((a : ℂ) + y * I) (by simpa using ha) (by simpa using ha3)
    have hi := (Complex.abs_im_le_norm
      (Complex.digamma ((a : ℂ) + y * I) - (Real.log (|y| + 2) : ℂ))).trans
      (by simpa using h)
    simpa [F', Real.norm_eq_abs] using hi
  exact norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y _ => (hd y).hasDerivWithinAt) (fun y _ => hb y) v
      (right_mem_Icc.mpr huv)

 theorem sharp_gamma_log_vertical (a u v : ℝ)
    (ha : 1 / 8 ≤ a) (ha3 : a ≤ 3) :
    |Real.log ‖Complex.Gamma ((a : ℂ) + v * I)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + u * I)‖| ≤
      (59 + |Real.eulerMascheroniConstant|) * |v - u| := by
  rcases le_total u v with huv | hvu
  · simpa only [abs_of_nonneg (sub_nonneg.mpr huv)] using
      sharp_gamma_log_vertical_ordered a u v ha ha3 huv
  · have h := sharp_gamma_log_vertical_ordered a v u ha ha3 hvu
    calc
      _ = |Real.log ‖Complex.Gamma ((a : ℂ) + u * I)‖ -
          Real.log ‖Complex.Gamma ((a : ℂ) + v * I)‖| := abs_sub_comm _ _
      _ ≤ _ := h
      _ = _ := by rw [abs_of_nonpos (sub_nonpos.mpr hvu)]; ring

 theorem sharp_gamma_vertical (a u v : ℝ) (ha : 1 / 8 ≤ a) (ha3 : a ≤ 3) :
    ‖Complex.Gamma ((a : ℂ) + v * I)‖ / ‖Complex.Gamma ((a : ℂ) + u * I)‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * |v - u|) := by
  have hGu : 0 < ‖Complex.Gamma ((a : ℂ) + u * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hGv : 0 < ‖Complex.Gamma ((a : ℂ) + v * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have h := (le_abs_self _).trans (sharp_gamma_log_vertical a u v ha ha3)
  rw [← Real.log_div hGv.ne' hGu.ne'] at h
  have he := Real.exp_le_exp.mpr h
  rwa [Real.exp_log (div_pos hGv hGu)] at he

 theorem sharp_gamma_quotient (a b t u : ℝ)
    (ha : 1 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    ‖Complex.Gamma ((b : ℂ) + (t + u) * I)‖ / ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * (b - a + |u|)) *
        (|t| + 2) ^ (b - a) := by
  have hn : ‖Complex.Gamma ((b : ℂ) + t * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hv := sharp_gamma_vertical b t (t + u) (ha.trans hab) hb
  simp only [add_sub_cancel_left] at hv
  calc
    _ = (‖Complex.Gamma ((b : ℂ) + (t + u) * I)‖ / ‖Complex.Gamma ((b : ℂ) + t * I)‖) *
        (‖Complex.Gamma ((b : ℂ) + t * I)‖ / ‖Complex.Gamma ((a : ℂ) + t * I)‖) := by
      field_simp
    _ ≤ Real.exp ((59 + |Real.eulerMascheroniConstant|) * |u|) *
        (Real.exp ((59 + |Real.eulerMascheroniConstant|) * (b - a)) *
        (|t| + 2) ^ (b - a)) :=
      by simpa only [Complex.ofReal_add] using
        mul_le_mul hv (sharp_gamma_horizontal_ordered a b t ha hab hb)
          (by positivity) (by positivity)
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

end Ostmann

end OAI
