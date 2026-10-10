import OAI.NumberTheory.TwoPointCorrelations.MRTFactoredReciprocal

namespace OAI

/-! An absolute Euler-factor bound on one short prime bin. Counting all
integers in the bin already suffices, so this local mixed-moment constant
requires no additional prime-distribution theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_short_bin_reciprocal_mass (P : Finset ℕ) {Y : ℕ} (hY : 0 < Y)
    (hP : P ⊆ Icc Y (2 * Y)) :
    (∑ p ∈ P, (1 : ℝ) / p) ≤ 2 := by
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hc : P.card ≤ 2 * Y := by
    have hh := card_le_card hP
    rw [Nat.card_Icc] at hh
    omega
  calc
    _ ≤ ∑ _p ∈ P, (1 : ℝ) / Y := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hYR (by exact_mod_cast (mem_Icc.mp (hP hp)).1)
    _ = (P.card : ℝ) / Y := by simp [div_eq_mul_inv]
    _ ≤ 2 := (div_le_iff₀ hYR).mpr (by exact_mod_cast hc)

lemma mrt_short_bin_reciprocal_square_mass (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) {Y : ℕ} (hY : 0 < Y)
    (hP : P ⊆ Icc Y (2 * Y)) :
    (∑ p ∈ P, ((1 : ℝ) / p) ^ 2) ≤ 1 := by
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ p ∈ P, (1 : ℝ) / p := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hmem
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hmem).two_le
      have hi : (1 : ℝ) / p ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) hp2
      nlinarith [show (0 : ℝ) ≤ 1 / (p : ℝ) by positivity]
    _ ≤ (1 / 2 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left (mrt_short_bin_reciprocal_mass P hY hP) (by norm_num)
    _ = 1 := by norm_num

theorem mrt_short_bin_euler_cube (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) {Y : ℕ} (hY : 0 < Y)
    (hP : P ⊆ Icc Y (2 * Y)) :
    (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 ≤ Real.exp 9 := by
  have hprod : (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ≤
      Real.exp (∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2)) := by
    rw [Real.exp_sum]
    apply prod_le_prod₀
    · intro p hmem
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hmem).two_le
      have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    · exact fun p hmem => mrt_prime_reciprocal_euler_bound (hp p hmem)
  have hn : 0 ≤ ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := by
    apply prod_nonneg
    intro p hmem
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hmem).two_le
    have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    exact inv_nonneg.mpr (by linarith)
  calc
    _ ≤ (Real.exp (∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2))) ^ 3 :=
      pow_le_pow_left₀ hn hprod 3
    _ = Real.exp (3 * ∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2)) := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [sum_add_distrib]
      linarith [mrt_short_bin_reciprocal_mass P hY hP,
        mrt_short_bin_reciprocal_square_mass P hp hY hP]

end TwoPointCorrelations

end OAI
