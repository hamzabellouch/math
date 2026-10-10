import Mathlib.Analysis.Calculus.MeanValue
import OAI.NumberTheory.Ostmann.ZeroDensity.GammaNormDerivative

namespace OAI

/-! # Gamma quotients with the exact horizontal power -/

namespace Ostmann

open Complex Set

 theorem sharp_gamma_log_horizontal_ordered (a b t : ℝ)
    (ha : 1 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    |Real.log ‖Complex.Gamma ((b : ℂ) + t * I)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ -
        (b - a) * Real.log (|t| + 2)| ≤
      (59 + |Real.eulerMascheroniConstant|) * (b - a) := by
  let F : ℝ → ℝ := fun x => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖ -
    x * Real.log (|t| + 2)
  let F' : ℝ → ℝ := fun x => (Complex.digamma ((x : ℂ) + t * I)).re -
    Real.log (|t| + 2)
  have hd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt F (F' x) x := by
    convert! (gamma_log_norm_horizontal x t (by linarith [hx.1])).sub
      ((hasDerivAt_id x).mul_const (Real.log (|t| + 2))) using 1
    simp only [F', one_mul]
  have hbound (x : ℝ) (hx : x ∈ Ico a b) : ‖F' x‖ ≤
      59 + |Real.eulerMascheroniConstant| := by
    have he := sharp_digamma_strip ((x : ℂ) + t * I)
      (by simp; linarith [hx.1]) (by simp; linarith [hx.2])
    have hr := (Complex.abs_re_le_norm
      (Complex.digamma ((x : ℂ) + t * I) - (Real.log (|t| + 2) : ℂ))).trans
      (by simpa using he)
    simpa [F', Real.norm_eq_abs] using hr
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x hx => (hd x hx).hasDerivWithinAt) hbound b (right_mem_Icc.mpr hab)
  change ‖F b - F a‖ ≤ _ at hm
  have he : F b - F a = Real.log ‖Complex.Gamma ((b : ℂ) + t * I)‖ -
      Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ -
      (b - a) * Real.log (|t| + 2) := by dsimp [F]; ring
  simpa only [he, Real.norm_eq_abs] using hm

 theorem sharp_gamma_horizontal_ordered (a b t : ℝ)
    (ha : 1 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    ‖Complex.Gamma ((b : ℂ) + t * I)‖ / ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * (b - a)) *
        (|t| + 2) ^ (b - a) := by
  have hGa : 0 < ‖Complex.Gamma ((a : ℂ) + t * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hGb : 0 < ‖Complex.Gamma ((b : ℂ) + t * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hh := le_abs_self (Real.log ‖Complex.Gamma ((b : ℂ) + t * I)‖ -
    Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ - (b - a) * Real.log (|t| + 2))
  have h := sharp_gamma_log_horizontal_ordered a b t ha hab hb
  have hlog : Real.log (‖Complex.Gamma ((b : ℂ) + t * I)‖ /
      ‖Complex.Gamma ((a : ℂ) + t * I)‖) ≤
      (59 + |Real.eulerMascheroniConstant|) * (b - a) +
        Real.log (|t| + 2) * (b - a) := by
    rw [Real.log_div hGb.ne' hGa.ne']
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (div_pos hGb hGa), Real.exp_add,
    ← Real.rpow_def_of_pos (by positivity : 0 < |t| + 2)] at hexp
  exact hexp

end Ostmann

end OAI
