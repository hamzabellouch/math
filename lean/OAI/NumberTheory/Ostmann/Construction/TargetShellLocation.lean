import Mathlib.Analysis.Complex.ExponentialBounds
import OAI.NumberTheory.Ostmann.Construction.FillerTargetScale

namespace OAI

/-! # Target windows lie inside the selected late block -/

namespace Ostmann

theorem target_window_in_late_block (k : ℕ) (hk : 20000 ≤ k) (U τ T : ℝ)
    (hτ : 0 < τ) (hτlo : U ≤ Real.log τ)
    (hτhi : Real.log τ ≤ U + 2 * (k : ℝ) / 10000)
    (hTlo : (2 : ℝ) ^ (k - 1) * τ / 4 ≤ T)
    (hThi : T ≤ 600 * (4 : ℝ) ^ k * τ) :
    U ≤ Real.log T - 2 * (k : ℝ) / 10000 ∧
      Real.log T - (k : ℝ) / 10000 ≤ U + 5 * k := by
  have hkr : (20000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : ((k - 1 : ℕ) : ℝ) = k - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hlower : 0 < (2 : ℝ) ^ (k - 1) * τ / 4 := by positivity
  have hT : 0 < T := hlower.trans_le hTlo
  have hlo := Real.log_le_log hlower hTlo
  have hhi := Real.log_le_log hT hThi
  rw [Real.log_div (by positivity) (by norm_num),
    Real.log_mul (by positivity) hτ.ne', Real.log_pow, hk1] at hlo
  rw [Real.log_mul (by positivity) hτ.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hhi
  have hlog2lo : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog4hi : Real.log 4 ≤ 2 := by rw [Real.log_four_eq]; linarith
  have hlog600 : Real.log 600 ≤ 600 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 600 by norm_num)
    linarith
  have hlowprod := mul_le_mul_of_nonneg_left hlog2lo (show 0 ≤ (k : ℝ) - 1 by linarith)
  have hhighprod := mul_le_mul_of_nonneg_left hlog4hi (Nat.cast_nonneg k)
  constructor <;> nlinarith

theorem target_window_below_cutoff (k : ℕ) (hk : 20000 ≤ k) (τ T : ℝ)
    (hτ : 0 < τ) (hThi : T ≤ 600 * (4 : ℝ) ^ k * τ) :
    T * Real.exp (-(k : ℝ) / 10000) < (1000 * (4 : ℝ) ^ k * τ) / 4 := by
  have hkr : (20000 : ℝ) ≤ k := by exact_mod_cast hk
  have hexp : 3 ≤ Real.exp ((k : ℝ) / 10000) := by
    have := Real.add_one_le_exp ((k : ℝ) / 10000)
    linarith
  have hsmall : Real.exp (-(k : ℝ) / 10000) ≤ 1 / 3 := by
    rw [show -(k : ℝ) / 10000 = -((k : ℝ) / 10000) by ring, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hexp
  have h1 := mul_le_mul_of_nonneg_right hThi (Real.exp_pos (-(k : ℝ) / 10000)).le
  have h2 := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ 600 * (4 : ℝ) ^ k * τ by positivity)
  have hpos : 0 < (4 : ℝ) ^ k * τ := by positivity
  nlinarith

theorem target_shell_scale (ε k T u : ℝ) (hT : 0 < T)
    (hlo : Real.log T - 2 * ε * k ≤ u)
    (hhi : u + 1 ≤ Real.log T - ε * k) :
    Real.exp (ε * k) * Real.exp u ≤ T ∧
      T ≤ Real.exp (2 * ε * k) * Real.exp u := by
  constructor
  · rw [← Real.exp_add, ← Real.exp_log hT]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_add, ← Real.exp_log hT]
    exact Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
