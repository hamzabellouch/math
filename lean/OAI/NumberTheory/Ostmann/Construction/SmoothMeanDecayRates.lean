import OAI.NumberTheory.Ostmann.ZeroDensity.LowZeroDecayRate

namespace OAI

/-! # Numerical decay for the remaining terms of the smooth explicit formula -/
namespace Ostmann
open Filter

/-- The conductor grows more slowly than `log X = exp L`. -/
theorem eventual_conductor_exponential_decay (a b C D : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, 0 ≤ q →
      q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      C * Real.exp (b * q - Real.exp L / 2) ≤ Real.exp (-D * L) := by
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left (4 * b * a)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hlin := ((isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 1 by norm_num)).const_mul_left (4 * |D + 1|)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hsmall, hlin, Real.tendsto_exp_atTop.eventually_ge_atTop C,
    eventually_ge_atTop (1 : ℝ)] with L hs hl hcoef hL
  intro q _ hq
  have hs' : 4 * b * a * L ≤ Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 4 * b * a * L), abs_of_pos (Real.exp_pos _), one_mul] using hs
  have hl' : 4 * |D + 1| * L ≤ Real.exp L := by
    simpa only [pow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 4 * |D + 1| * L), abs_of_pos (Real.exp_pos _)] using hl
  have hg : b * q ≤ Real.exp L / 4 := by
    have hm := mul_le_mul_of_nonneg_right hs' (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    have he : Real.exp ((1 / 10 : ℝ) * L) * Real.exp ((9 / 10 : ℝ) * L) =
        Real.exp L := by rw [← Real.exp_add]; congr 1; ring
    rw [he] at hm
    have hmq := mul_le_mul_of_nonneg_left hq hb
    nlinarith
  calc
    _ ≤ Real.exp L * Real.exp (b * q - Real.exp L / 2) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = Real.exp (L + b * q - Real.exp L / 2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_right (le_abs_self (D + 1)) (by linarith : 0 ≤ L)
      linarith)

/-- The high-zero tail decays when `log Q` is at least `L²`. -/
theorem eventual_conductor_negative_decay (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, L ^ 2 ≤ q →
      C * Real.exp (-q) ≤ Real.exp (-D * L) := by
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop C,
    eventually_ge_atTop (max 1 (D + 1))] with L hC' hL
  intro q hq
  have hL0 : 0 ≤ L := le_trans (by norm_num) ((le_max_left _ _).trans hL)
  have hDL : (D + 1) * L ≤ L ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hL) hL0
    nlinarith
  calc
    _ ≤ Real.exp L * Real.exp (-q) := mul_le_mul_of_nonneg_right hC' (Real.exp_nonneg _)
    _ = Real.exp (L - q) := by rw [← Real.exp_add]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
