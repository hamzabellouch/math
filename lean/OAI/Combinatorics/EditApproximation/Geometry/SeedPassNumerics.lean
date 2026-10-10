import OAI.Combinatorics.EditApproximation.Geometry.DomainExponential
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! Numerical amplification for the literal H²-copy seed update and
the finite sequence of refinement passes. -/

namespace EditApproximation

theorem seed_copy_binary_tail (copies ell : ℕ) (hell : 64 ≤ ell) :
    (2 : ℝ) ^ copies * (1 / (ell : ℝ)) ^ (copies - copies / 2) ≤
      Real.exp (-(copies : ℝ)) := by
  let k := copies - copies / 2
  have hcopies : copies ≤ 2 * k := by dsimp only [k]; omega
  have hellR : (64 : ℝ) ≤ ell := by exact_mod_cast hell
  have hellpos : (0 : ℝ) < ell := by linarith only [hellR]
  have hscale : (4 : ℝ) / ell ≤ 1 / 16 := by
    apply (div_le_iff₀ hellpos).2
    linarith only [hellR]
  have hexp2 : Real.exp (2 : ℝ) ≤ 16 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have he := Real.exp_one_lt_three
    have hep := Real.exp_pos (1 : ℝ)
    nlinarith only [he, hep]
  have hexpinv : (1 / 16 : ℝ) ≤ Real.exp (-2) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hexp2
  calc
    _ ≤ (2 : ℝ) ^ (2 * k) * (1 / (ell : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcopies) (by positivity)
    _ = ((4 : ℝ) / ell) ^ k := by rw [pow_mul, ← mul_pow]; congr 1; norm_num [div_eq_mul_inv]
    _ ≤ (1 / 16 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hscale k
    _ ≤ Real.exp (-2) ^ k := pow_le_pow_left₀ (by norm_num) hexpinv k
    _ = Real.exp (-2 * (k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-(copies : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hc : (copies : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hcopies
      linarith only [hc]

theorem seed_state_union_numeric (H domain : ℝ)
    (hdomain : domain ≤ Real.exp (10 * H)) :
    domain * Real.exp (-(H ^ 2)) ≤ Real.exp (10 * H - H ^ 2) := by
  calc
    _ ≤ Real.exp (10 * H) * Real.exp (-(H ^ 2)) :=
      mul_le_mul_of_nonneg_right hdomain (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1

theorem seed_pass_union_numeric (H : ℝ) (hH : 100 ≤ H) :
    H * Real.exp (10 * H - H ^ 2) ≤ 1 / 100 := by
  have hH0 : 0 ≤ H := by linarith only [hH]
  have hquadratic := mul_nonneg hH0 (show 0 ≤ H - 100 by linarith only [hH])
  have hexponent : 10 * H - H ^ 2 ≤ -2 * H := by nlinarith only [hquadratic, hH]
  have hHexp : H ≤ Real.exp H := by linarith only [Real.add_one_le_exp H]
  have hexp100 : (100 : ℝ) ≤ Real.exp H := hH.trans hHexp
  calc
    _ ≤ H * Real.exp (-2 * H) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hH0
    _ ≤ Real.exp H * Real.exp (-2 * H) := mul_le_mul_of_nonneg_right hHexp (Real.exp_pos _).le
    _ = Real.exp (-H) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 / 100 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) hexp100

theorem computed_seed_total_failure (N passes : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hpasses : passes ≤ inputHeight N) :
    (1 / 100 : ℝ) + passes * Real.exp (10 * inputHeight N - (inputHeight N : ℝ) ^ 2) < 1 / 10 := by
  have hlogs := inputSmallLog_bounds N hN
  have hheight : 7 ≤ heightExponent N := by omega
  have hH100 : 100 ≤ inputHeight N := (by norm_num : 100 ≤ (2 : ℕ) ^ 7).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hheight)
  have hpassR : (passes : ℝ) ≤ inputHeight N := by exact_mod_cast hpasses
  have hbound := (mul_le_mul_of_nonneg_right hpassR
    (Real.exp_pos (10 * inputHeight N - (inputHeight N : ℝ) ^ 2)).le).trans
    (seed_pass_union_numeric (inputHeight N) (by exact_mod_cast hH100))
  linarith only [hbound]

end EditApproximation

end OAI
