import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftScale

namespace OAI

/-! The physical interval scales imply every endpoint-size condition used
in the translated rough-shift average. -/

namespace TwoPointCorrelations

open Filter

theorem rough_shift_ratio (L : ℝ) (hL : 10 ≤ L) (D Y : ℕ)
    (hD : (D : ℝ) ≤ Real.exp (2 * L))
    (hY : Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ Y) :
    (D : ℝ) / Y ≤ L ^ (-21 / 20 : ℝ) := by
  have hL₁ : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hYp : (0 : ℝ) < Y := (Real.exp_pos _).trans_le hY
  have hp : L ^ (2 : ℝ) ≤ L ^ (1000 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL₁ (by norm_num)
  have hsq : (10 : ℝ) * L ≤ L ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hL hLp.le
    nlinarith only [hh]
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hgap : 2 * L - (1 / 2 : ℝ) * L ^ (1000 : ℝ) ≤
      Real.log L * (-21 / 20 : ℝ) := by
    norm_num only [Real.rpow_two] at hp
    nlinarith only [hp, hsq, hlog, hL]
  calc
    _ ≤ Real.exp (2 * L) / Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) :=
      div_le_div₀ (Real.exp_pos _).le hD (Real.exp_pos _) hY
    _ = Real.exp (2 * L - (1 / 2 : ℝ) * L ^ (1000 : ℝ)) := (Real.exp_sub _ _).symm
    _ ≤ _ := by
      rw [Real.rpow_def_of_pos hLp (-21 / 20 : ℝ)]
      exact Real.exp_le_exp.mpr hgap

theorem eventually_rough_interval_lower :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℕ,
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D → 10 ≤ D := by
  have hg := ((Real.tendsto_exp_atTop.comp
    (tendsto_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num))).const_mul_atTop
      (show (0 : ℝ) < 1 / 2 by norm_num)).eventually (eventually_ge_atTop 10)
  filter_upwards [hg] with L hL
  intro D hD
  exact_mod_cast hL.trans hD

end TwoPointCorrelations

end OAI
