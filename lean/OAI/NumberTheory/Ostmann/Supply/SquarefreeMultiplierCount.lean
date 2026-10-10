import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace OAI

/-! # An elementary positive-density supply of squarefree multipliers -/

namespace Ostmann
open scoped Classical BigOperators

private theorem reciprocal_square_step (x : ℝ) (hx : 0 < x) :
    (x + 1)⁻¹ ^ 2 ≤ x⁻¹ - (x + 1)⁻¹ := by
  have hx1 : 0 < x + 1 := by linarith
  have h : (x + 1)⁻¹ ^ 2 ≤ (x * (x + 1))⁻¹ := by
    rw [inv_pow, inv_le_inv₀ (sq_pos_of_pos hx1) (mul_pos hx hx1)]
    nlinarith
  calc
    _ ≤ (x * (x + 1))⁻¹ := h
    _ = x⁻¹ - (x + 1)⁻¹ := by field_simp; ring

theorem sum_reciprocal_squares_le_three_quarters (N : ℕ) :
    (∑ d ∈ Finset.Icc 2 N, (d : ℝ)⁻¹ ^ 2) ≤ 3 / 4 := by
  by_cases hN : 2 ≤ N
  · have hh : ∀ N : ℕ, N ≥ 2 → (∑ d ∈ Finset.Icc 2 N, (d : ℝ)⁻¹ ^ 2) ≤
        3 / 4 - (N : ℝ)⁻¹ := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => norm_num
      | succ N hN ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        have hs := reciprocal_square_step (N : ℝ) hp
        push_cast
        linarith
    exact (hh N hN).trans (sub_le_self _ (by positivity))
  · have he : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    norm_num [he]

noncomputable def nonSquarefreeMultipliers (U : ℕ) : Finset ℕ :=
  (Finset.range (U + 1)).filter (fun u => u ≠ 0 ∧ ¬ Squarefree u)

noncomputable def positiveMultiplesUpTo (U d : ℕ) : Finset ℕ :=
  (Finset.range (U + 1)).filter (fun u => u ≠ 0 ∧ d ∣ u)

theorem nonSquarefreeMultipliers_subset (U : ℕ) :
    nonSquarefreeMultipliers U ⊆ (Finset.Icc 2 U).biUnion
      (fun d => positiveMultiplesUpTo U (d * d)) := by
  intro u hu
  obtain ⟨huU, hu0, hsq⟩ := Finset.mem_filter.mp hu
  have hex : ∃ p, Nat.Prime p ∧ p * p ∣ u := by
    by_contra h
    apply hsq
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hd
    exact h ⟨p, hp, hd⟩
  obtain ⟨p, hp, hd⟩ := hex
  have hpu : p ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero hu0)
    (dvd_trans (dvd_mul_right p p) hd)
  refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩, ?_⟩
  · have := Finset.mem_range.mp huU
    omega
  · exact Finset.mem_filter.mpr ⟨huU, hu0, hd⟩

theorem nonSquarefreeMultipliers_card_le (U : ℕ) :
    (nonSquarefreeMultipliers U).card ≤ ∑ d ∈ Finset.Icc 2 U, U / (d * d) := by
  apply (Finset.card_le_card (nonSquarefreeMultipliers_subset U)).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro d _
  exact (Nat.card_multiples' U (d * d)).le

theorem nonSquarefreeMultipliers_real_card_le (U : ℕ) :
    ((nonSquarefreeMultipliers U).card : ℝ) ≤ (3 / 4) * U := by
  calc
    _ ≤ ((∑ d ∈ Finset.Icc 2 U, U / (d * d) : ℕ) : ℝ) := by
      exact_mod_cast nonSquarefreeMultipliers_card_le U
    _ ≤ ∑ d ∈ Finset.Icc 2 U, (U : ℝ) * (d : ℝ)⁻¹ ^ 2 := by
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro d _
      simpa only [Nat.cast_mul, mul_inv_rev, div_eq_mul_inv, pow_two] using
        (Nat.cast_div_le (m := U) (n := d * d) (α := ℝ))
    _ = (U : ℝ) * ∑ d ∈ Finset.Icc 2 U, (d : ℝ)⁻¹ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ (U : ℝ) * (3 / 4) := mul_le_mul_of_nonneg_left
      (sum_reciprocal_squares_le_three_quarters U) (Nat.cast_nonneg U)
    _ = _ := mul_comm _ _

end Ostmann

end OAI
