import Mathlib.Data.Nat.Choose.Sum
import OAI.NumberTheory.Ostmann.Characters.PublishedBonami

namespace OAI

/-! # The elementary two-point estimate for the required Bonami bound -/

namespace Ostmann

open Finset
open scoped BigOperators

theorem bonami_choose_bound (l j : ℕ) (hl : 0 < l) :
    (2 * l).choose (2 * j) ≤ l.choose j * (2 * l - 1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hj : j + 1 ≤ l
    · have hstep1 := Nat.choose_succ_right_eq (2 * l) (2 * j + 1)
      have hstep2 := Nat.choose_succ_right_eq (2 * l) (2 * j)
      have hsmall := Nat.choose_succ_right_eq l j
      have heven : 2 * l - 2 * j = 2 * (l - j) := by omega
      have hodd : 2 * l - (2 * j + 1) ≤ (2 * l - 1) * (2 * j + 1) := by
        have hone : 1 ≤ 2 * j + 1 := by omega
        have hmono := Nat.mul_le_mul_left (2 * l - 1) hone
        omega
      have hid : (2 * l).choose (2 * (j + 1)) * (2 * j + 2) * (2 * j + 1) =
          (2 * l).choose (2 * j) * (2 * (l - j)) * (2 * l - (2 * j + 1)) := by
        calc
          _ = ((2 * l).choose (2 * j + 1) * (2 * l - (2 * j + 1))) *
              (2 * j + 1) := by rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, hstep1]
          _ = ((2 * l).choose (2 * j + 1) * (2 * j + 1)) *
              (2 * l - (2 * j + 1)) := by ring
          _ = _ := by rw [hstep2, heven]
      have hbound : (2 * l).choose (2 * (j + 1)) * ((2 * j + 2) * (2 * j + 1)) ≤
          (l.choose (j + 1) * (2 * l - 1) ^ (j + 1)) *
            ((2 * j + 2) * (2 * j + 1)) := by
        calc
          _ = (2 * l).choose (2 * j) * (2 * (l - j)) *
              (2 * l - (2 * j + 1)) := by rw [← Nat.mul_assoc, hid]
          _ ≤ (l.choose j * (2 * l - 1) ^ j) * (2 * (l - j)) *
              ((2 * l - 1) * (2 * j + 1)) := by gcongr
          _ = (l.choose j * (l - j)) * (2 * l - 1) ^ (j + 1) *
              (2 * (2 * j + 1)) := by rw [pow_succ]; ring
          _ = _ := by rw [← hsmall]; ring
      exact Nat.le_of_mul_le_mul_right hbound (by positivity)
    · rw [Nat.choose_eq_zero_of_lt (by omega : 2 * l < 2 * (j + 1))]
      exact Nat.zero_le _

private theorem sum_range_double (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range (2 * n), f i) = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

private theorem even_power_binomial (x y : ℝ) (l : ℕ) :
    ((x + y) ^ (2 * l) + (x - y) ^ (2 * l)) / 2 =
      ∑ j ∈ range (l + 1), y ^ (2 * j) * x ^ (2 * (l - j)) *
        ((2 * l).choose (2 * j) : ℝ) := by
  have hsum : (x + y) ^ (2 * l) + (x - y) ^ (2 * l) =
      ∑ i ∈ range (2 * l + 1),
        (y ^ i + (-y) ^ i) * x ^ (2 * l - i) * ((2 * l).choose i : ℝ) := by
    rw [show x + y = y + x by ring, show x - y = -y + x by ring,
      add_pow, add_pow, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum, sum_range_succ, sum_range_double, sum_range_succ]
  have heven (j : ℕ) : (-y) ^ (2 * j) = y ^ (2 * j) := by
    rw [pow_mul, neg_sq, ← pow_mul]
  have hodd (j : ℕ) : (-y) ^ (2 * j + 1) = -(y ^ (2 * j + 1)) := by
    rw [pow_succ, pow_succ, heven]
    ring
  simp_rw [heven, hodd, add_neg_cancel, zero_mul, add_zero]
  have hsub : ∀ j ∈ range l, 2 * l - 2 * j = 2 * (l - j) := by
    intro j hj
    omega
  have hrew : (∑ j ∈ range l,
      (y ^ (2 * j) + y ^ (2 * j)) * x ^ (2 * l - 2 * j) *
        ((2 * l).choose (2 * j) : ℝ)) =
      2 * ∑ j ∈ range l, y ^ (2 * j) * x ^ (2 * (l - j)) *
        ((2 * l).choose (2 * j) : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [hsub j hj]
    ring
  rw [hrew]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]
  ring

/-- Bonami's required even-moment inequality on one Boolean coordinate. -/
theorem bonami_two_point (x y : ℝ) (l : ℕ) (hl : 0 < l) :
    (|x + y| ^ (2 * l) + |x - y| ^ (2 * l)) / 2 ≤
      (x ^ 2 + (2 * l - 1 : ℕ) * y ^ 2) ^ l := by
  have he (z : ℝ) (n : ℕ) : 0 ≤ z ^ (2 * n) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  rw [← abs_pow, ← abs_pow, abs_of_nonneg (he _ _),
    abs_of_nonneg (he _ _), even_power_binomial]
  rw [show x ^ 2 + ((2 * l - 1 : ℕ) : ℝ) * y ^ 2 =
    ((2 * l - 1 : ℕ) : ℝ) * y ^ 2 + x ^ 2 by ring, add_pow]
  apply sum_le_sum
  intro j hj
  have hc : ((2 * l).choose (2 * j) : ℝ) ≤
      (l.choose j : ℝ) * ((2 * l - 1 : ℕ) : ℝ) ^ j := by
    exact_mod_cast bonami_choose_bound l j hl
  calc
    _ ≤ y ^ (2 * j) * x ^ (2 * (l - j)) *
        ((l.choose j : ℝ) * ((2 * l - 1 : ℕ) : ℝ) ^ j) := by
      exact mul_le_mul_of_nonneg_left hc (mul_nonneg (he _ _) (he _ _))
    _ = _ := by simp only [mul_pow, pow_mul]; ring

end Ostmann

end OAI
