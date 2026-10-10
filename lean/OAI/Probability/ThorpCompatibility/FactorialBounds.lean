import Mathlib

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma log_step_bound (n : ℕ) :
    ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) - (n : ℝ) * Real.log n ≤
      Real.log ((n : ℝ) + 1) + 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hn1 hn0)) hn0.le
  rw [Real.log_div hn1.ne' hn0.ne'] at h
  have hr : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
    field_simp
    ring
  rw [hr] at h
  nlinarith

lemma log_descFactorial_integral (n k : ℕ) (hk : k ≤ n) :
    (n : ℝ) * Real.log n - (n - k : ℕ) * Real.log (n - k : ℕ) - k ≤
      Real.log (n.descFactorial k : ℝ) := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hk
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk' : k ≤ n := Nat.le_of_succ_le_succ hk
      have h₁ := ih k hk'
      have h₂ := log_step_bound n
      have hd : (n.descFactorial k : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.descFactorial_pos.mpr hk').ne'
      rw [Nat.succ_descFactorial_succ, Nat.cast_mul,
        Real.log_mul (by positivity) hd]
      simp only [Nat.succ_sub_succ_eq_sub, Nat.cast_succ] at *
      linarith

lemma log_descFactorial_lower (n k : ℕ) (hk : k ≤ n) :
    (k : ℝ) * (Real.log n - 1) ≤ Real.log (n.descFactorial k : ℝ) := by
  have h := log_descFactorial_integral n k hk
  have hnk : (n - k : ℕ) * Real.log (n - k : ℕ) ≤
      (n - k : ℕ) * Real.log n := by
    by_cases hz : n - k = 0
    · simp [hz]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
    exact_mod_cast Nat.sub_le n k
  rw [Nat.cast_sub hk] at h hnk
  nlinarith

lemma descFactorial_exponential_lower (n k : ℕ) (hk : k ≤ n) :
    ((n : ℝ) / Real.exp 1) ^ k ≤ (n.descFactorial k : ℝ) := by
  by_cases hk0 : k = 0
  · simp [hk0]
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (Nat.pos_of_ne_zero hk0) hk
  have hd : (0 : ℝ) < n.descFactorial k := by
    exact_mod_cast Nat.descFactorial_pos.mpr hk
  apply (Real.log_le_log_iff (pow_pos (div_pos hn0 (Real.exp_pos _)) _) hd).mp
  rw [Real.log_pow, Real.log_div hn0.ne' (Real.exp_ne_zero _), Real.log_exp]
  exact log_descFactorial_lower n k hk

end ThorpCompatibility

end OAI
