import Mathlib

namespace OAI

noncomputable section

namespace Problem315

theorem switchDenominator_le (n : ℕ) :
    24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ) ≤ (n : ℝ) ^ 6 := by
  have hc := Nat.choose_le_pow_div (α := ℝ) 4 n
  norm_num at hc
  nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (n : ℝ))]

theorem switchDenominator_pos (n : ℕ) (hn : 4 ≤ n) :
    0 < 24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ) := by
  have hn0 : 0 < n := by omega
  have hc : 0 < Nat.choose n 4 := Nat.choose_pos hn
  positivity

theorem numeric_mixing_bound (n N : ℕ) (hn : 4 ≤ n)
    (hN : 1 ≤ N) (hsize : N ≤ 2 ^ (n * n)) :
    Real.sqrt (N : ℝ) / 2 *
      Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
        (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) ≤ 1 / 4 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have hpow : (N : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
    calc
      (N : ℝ) ≤ (2 : ℝ) ^ (n * n) := by exact_mod_cast hsize
      _ ≤ Real.exp 1 ^ (n * n) := pow_le_pow_left₀ (by norm_num) hexp _
      _ = Real.exp ((n : ℝ) ^ 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have hsqrt : Real.sqrt (N : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
    exact (Real.sqrt_le_self_iff.mpr (Or.inr hNR)).trans hpow
  have hden := switchDenominator_pos n hn
  have hdenle := switchDenominator_le n
  have hratio : 2 * (n : ℝ) ^ 2 ≤
      ((2 * n ^ 8 : ℕ) : ℝ) /
        (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)) := by
    apply (le_div_iff₀ hden).2
    have hh := mul_le_mul_of_nonneg_left hdenle (show 0 ≤ 2 * (n : ℝ) ^ 2 by positivity)
    push_cast
    nlinarith [hh]
  have hdecay : Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
        (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) ≤
      Real.exp (-2 * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  calc
    Real.sqrt (N : ℝ) / 2 * Real.exp
        (- ((2 * n ^ 8 : ℕ) : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))
      ≤ Real.exp ((n : ℝ) ^ 2) / 2 * Real.exp (-2 * (n : ℝ) ^ 2) := by
        exact mul_le_mul (div_le_div_of_nonneg_right hsqrt (by norm_num)) hdecay
          (Real.exp_nonneg _) (by positivity)
    _ = Real.exp (- (n : ℝ) ^ 2) / 2 := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (1 / 2 : ℝ) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le (by norm_num)
      exact hexp.trans (Real.exp_le_exp.mpr (by nlinarith))
    _ = 1 / 4 := by norm_num

end Problem315

end

end OAI
