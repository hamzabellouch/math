import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! # Prior domination for a repeated compensation-prime sample -/

namespace Ostmann

open scoped BigOperators

/-- Keep one occurrence's prior and charge the other occurrences their pointwise bounds. -/
theorem repeated_prior_weight_le {I : Type*} [DecidableEq I]
    (S : Finset I) (i : I) (hi : i ∈ S) (μ : I → ℝ) (b E : ℝ)
    (hb : 2 ≤ b) (hμ : ∀ j ∈ S, 0 ≤ μ j)
    (hbound : ∀ j ∈ S.erase i, b * μ j ≤ E) :
    (∏ j ∈ S, b * μ j) / (b - 1) ≤ 2 * μ i * E ^ (S.card - 1) := by
  have hb0 : 0 ≤ b := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have hprod : (∏ j ∈ S.erase i, b * μ j) ≤ E ^ (S.card - 1) := by
    have h := Finset.prod_le_prod₀
      (fun j hj => mul_nonneg hb0 (hμ j (Finset.mem_of_mem_erase hj))) hbound
    simpa only [Finset.prod_const, Finset.card_erase_of_mem hi] using h
  have hquot : b / (b - 1) ≤ 2 := by
    apply (div_le_iff₀ hb1).mpr
    linarith
  calc
    _ = (b / (b - 1)) * μ i * ∏ j ∈ S.erase i, b * μ j := by
      rw [← Finset.prod_erase_mul S (fun j => b * μ j) hi]
      ring
    _ ≤ 2 * μ i * ∏ j ∈ S.erase i, b * μ j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hquot (hμ i hi))
        (Finset.prod_nonneg fun j hj => mul_nonneg hb0 (hμ j (Finset.mem_of_mem_erase hj)))
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) (hμ i hi))

/-- Summing a repeated sample loses no factor from the number of possible prime values. -/
theorem repeated_prior_sum_le {I B : Type*} [DecidableEq I]
    (S : Finset I) (i : I) (hi : i ∈ S) (P : Finset B)
    (μ : I → B → ℝ) (value : B → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hb : ∀ b ∈ P, 2 ≤ value b) (hμ : ∀ j ∈ S, ∀ b ∈ P, 0 ≤ μ j b)
    (hbound : ∀ j ∈ S.erase i, ∀ b ∈ P, value b * μ j b ≤ E)
    (hmass : (∑ b ∈ P, μ i b) ≤ 1) :
    (∑ b ∈ P, (∏ j ∈ S, value b * μ j b) / (value b - 1)) ≤
      2 * E ^ (S.card - 1) := by
  calc
    _ ≤ ∑ b ∈ P, 2 * μ i b * E ^ (S.card - 1) := by
      apply Finset.sum_le_sum
      intro b hbP
      exact repeated_prior_weight_le S i hi (fun j => μ j b) (value b) E (hb b hbP)
        (fun j hj => hμ j hj b hbP) (fun j hj => hbound j hj b hbP)
    _ = 2 * (∑ b ∈ P, μ i b) * E ^ (S.card - 1) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ _ := by
      have hp : 0 ≤ E ^ (S.card - 1) := pow_nonneg hE _
      nlinarith

end Ostmann

end OAI
