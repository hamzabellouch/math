import Mathlib

namespace OAI

namespace PolynomialVacuumBridge.Corridor

 

theorem log_square_exponential_beats_power (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (A : ℝ) : ∀ᶠ h : ℕ in Filter.atTop,
      C*((h : ℝ)+1)^2 * Real.exp (-c*((h : ℝ)*(Real.log (h : ℝ))^2)/(h+1)) ≤
        (h : ℝ)^(-A) := by
  let B := |A+2|+|Real.log (4*C)|
  let K := max 1 (2*B/c)
  have hlog : Filter.Tendsto (fun h : ℕ => Real.log (h : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1,hlog.eventually (Filter.eventually_ge_atTop K)] with h hh hL
  have hx : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hxp : (0 : ℝ) < h := lt_of_lt_of_le zero_lt_one hx
  have hH : (0 : ℝ) < (h : ℝ)+1 := by positivity
  have hL1 : 1 ≤ Real.log (h : ℝ) := (le_max_left _ _).trans hL
  have hLK : 2*B/c ≤ Real.log (h : ℝ) := (le_max_right _ _).trans hL
  have hcL : B ≤ c/2*Real.log (h : ℝ) := by
    have he := (div_le_iff₀ hc).mp hLK
    nlinarith
  have hpoly : C*((h : ℝ)+1)^2 ≤ 4*C*(h : ℝ)^2 := by
    nlinarith [mul_nonneg hC.le (show 0 ≤ (h : ℝ)-1 by linarith)]
  have hexp : Real.exp (-c*((h : ℝ)*(Real.log (h : ℝ))^2)/(h+1)) ≤
      Real.exp (-(c/2)*(Real.log (h : ℝ))^2) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hH).mpr
    nlinarith [mul_nonneg (show 0 ≤ c*(Real.log (h : ℝ))^2 by positivity)
      (show 0 ≤ (h : ℝ)-1 by linarith)]
  have hbound : Real.log (4*C)+2*Real.log (h : ℝ) + -(c/2)*(Real.log (h : ℝ))^2 ≤
      Real.log (h : ℝ)*(-A) := by
    have hb0 : 0 ≤ B := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have habs : A+2 ≤ |A+2| := le_abs_self _
    have hconst : Real.log (4*C) ≤ |Real.log (4*C)| := le_abs_self _
    have hm := mul_le_mul_of_nonneg_right hcL (by linarith : 0 ≤ Real.log (h : ℝ))
    have hm' := mul_le_mul_of_nonneg_right habs (by linarith : 0 ≤ Real.log (h : ℝ))
    have hconst' := mul_le_mul_of_nonneg_left hL1 (abs_nonneg (Real.log (4*C)))
    dsimp [B] at hm
    nlinarith
  calc
    _ ≤ 4*C*(h : ℝ)^2 * Real.exp (-(c/2)*(Real.log (h : ℝ))^2) :=
      mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
    _ = Real.exp (Real.log (4*C)+2*Real.log (h : ℝ) + -(c/2)*(Real.log (h : ℝ))^2) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by positivity : 0 < 4*C),two_mul,
        Real.exp_add,Real.exp_log hxp]
      ring
    _ ≤ Real.exp (Real.log (h : ℝ)*(-A)) := Real.exp_le_exp.mpr hbound
    _ = (h : ℝ)^(-A) := (Real.rpow_def_of_pos hxp (-A)).symm

end PolynomialVacuumBridge.Corridor

end OAI
