import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace OAI

/-!
# The uniform binomial estimate for free-word cuts

This supplies the numerical estimate used to sum the preservation cuts in
§3 of the manuscript. Its bound is independent of the word length.
-/

namespace KadisonKastler

open Finset

private theorem choose_monotone_to_half {m i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ m / 2) : m.choose i ≤ m.choose j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem choose_two_le_interior {m p : ℕ} (hp : 2 ≤ p) (hpm : p + 2 ≤ m) :
    m.choose 2 ≤ m.choose p := by
  by_cases hhalf : p ≤ m / 2
  · exact choose_monotone_to_half hp hhalf
  · rw [← Nat.choose_symm (show p ≤ m by omega)]
    exact choose_monotone_to_half (by omega) (by omega)

private theorem inv_sqrt_choose_interior {m p : ℕ} (hm : 4 ≤ m)
    (hp : 2 ≤ p) (hpm : p + 2 ≤ m) :
    1 / Real.sqrt (m.choose p : ℝ) ≤ 2 / (m : ℝ) := by
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hchoose : (m : ℝ) * (m - 1) / 2 ≤ (m.choose p : ℝ) := by
    rw [← Nat.cast_choose_two]
    exact_mod_cast choose_two_le_interior hp hpm
  have hs : (m : ℝ) / 2 ≤ Real.sqrt (m.choose p : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    nlinarith
  apply (div_le_div_iff₀ (by nlinarith : 0 < Real.sqrt (m.choose p : ℝ))
    (by linarith : (0 : ℝ) < m)).mpr
  nlinarith

private theorem sum_split_four (f : ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ range (n + 5), f p) = f 0 + f 1 +
      (∑ p ∈ range (n + 1), f (p + 2)) + f (n + 3) + f (n + 4) := by
  rw [show n + 5 = (2 + (n + 1)) + 2 by omega, sum_range_add, sum_range_add]
  have htwo (g : ℕ → ℝ) : (∑ p ∈ range 2, g p) = g 0 + g 1 := by
    simp [sum_range_succ]
  rw [htwo, htwo]
  simp [add_assoc, add_comm, add_left_comm]

/-- The sum of the inverse square roots of one row of Pascal's triangle
is at most five, uniformly in that row. This is the preservation-cut
constant in the free projection-word estimate. -/
theorem sum_inv_sqrt_choose_le_five (m : ℕ) :
    (∑ p ∈ range (m + 1), 1 / Real.sqrt (m.choose p : ℝ)) ≤ 5 := by
  by_cases hm : 4 ≤ m
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hlast : (4 + n).choose (n + 3) = 4 + n := by
      have := Nat.choose_symm (n := 4 + n) (k := 1) (by omega)
      simpa [add_comm] using this
    have htop : (4 + n).choose (n + 4) = 1 := by
      rw [show n + 4 = 4 + n by omega, Nat.choose_self]
    rw [show 4 + n + 1 = n + 5 by omega, sum_split_four]
    have hmid : (∑ p ∈ range (n + 1),
        1 / Real.sqrt ((4 + n).choose (p + 2) : ℝ)) ≤
        (n + 1 : ℝ) * (2 / (4 + n : ℝ)) := by
      calc
        _ ≤ ∑ _p ∈ range (n + 1), 2 / (4 + n : ℝ) := by
          apply sum_le_sum
          intro p hp
          simpa using inv_sqrt_choose_interior (m := 4 + n) (p := p + 2)
            (by omega) (by omega) (by have := mem_range.mp hp; omega)
        _ = _ := by simp
    have hmid_two : (n + 1 : ℝ) * (2 / (4 + n : ℝ)) ≤ 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 + n)).mpr
      linarith
    have hsqrt : (2 : ℝ) ≤ Real.sqrt (4 + n : ℝ) := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
      norm_num
    have hedge : 1 / Real.sqrt (4 + n : ℝ) ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num) hsqrt
    simp only [Nat.choose_zero_right, Nat.cast_one, Real.sqrt_one, div_one,
      Nat.choose_one_right, hlast, htop, Nat.cast_add, Nat.cast_ofNat] at *
    linarith
  · interval_cases m <;> norm_num [sum_range_succ, Nat.choose]
    all_goals
      have hs : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      have ht : (1 : ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      have hs' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs
      have ht' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ht
      norm_num at hs' ht'
      linarith

end KadisonKastler

end OAI
