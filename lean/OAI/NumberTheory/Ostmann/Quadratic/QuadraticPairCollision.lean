import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Coincidences between two monic split quadratics

Distinct unordered pairs give monic quadratics whose equality can hold at
at most one point. This is the counting step in the fourth-moment estimate.
-/

namespace Ostmann

/-- Equality at two distinct points forces equality of the unordered roots. -/
theorem quadraticPair_eq_of_two_points {K : Type*} [Field K]
    (b₁ b₂ b₃ b₄ a a' : K) (haa : a ≠ a')
    (ha : (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))
    (ha' : (a' - b₁) * (a' - b₂) = (a' - b₃) * (a' - b₄)) :
    (b₁ = b₃ ∧ b₂ = b₄) ∨ (b₁ = b₄ ∧ b₂ = b₃) := by
  have hlin : (a - a') * (b₁ + b₂ - b₃ - b₄) = 0 := by
    linear_combination -ha + ha'
  have hsum : b₁ + b₂ = b₃ + b₄ := by
    have hzero := (mul_eq_zero.mp hlin).resolve_left (sub_ne_zero.mpr haa)
    linear_combination hzero
  have hprod : b₁ * b₂ = b₃ * b₄ := by
    linear_combination ha + a * hsum
  have hroot : (b₁ - b₃) * (b₁ - b₄) = 0 := by
    linear_combination b₁ * hsum - hprod
  rcases mul_eq_zero.mp hroot with h | h
  · left
    have h₁₃ : b₁ = b₃ := sub_eq_zero.mp h
    refine ⟨h₁₃, ?_⟩
    linear_combination hsum - h₁₃
  · right
    have h₁₄ : b₁ = b₄ := sub_eq_zero.mp h
    refine ⟨h₁₄, ?_⟩
    linear_combination hsum - h₁₄

/-- Off the two diagonals, there is at most one coincidence. -/
theorem quadraticPair_collision_card_le_one {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (b₁ b₂ b₃ b₄ : K)
    (hdiag : ¬ ((b₁ = b₃ ∧ b₂ = b₄) ∨ (b₁ = b₄ ∧ b₂ = b₃))) :
    (Finset.univ.filter (fun a : K =>
      (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha a' ha'
  by_contra hne
  exact hdiag (quadraticPair_eq_of_two_points b₁ b₂ b₃ b₄ a a' hne
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp ha').2)

/-- The two diagonal pairings account for every exceptional collision fiber. -/
theorem quadraticPair_collision_count_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (b₁ b₂ b₃ b₄ : K) :
    ((Finset.univ.filter (fun a : K =>
      (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ) ≤
      1 + (Fintype.card K : ℝ) *
        ((if b₁ = b₃ ∧ b₂ = b₄ then 1 else 0) +
          (if b₁ = b₄ ∧ b₂ = b₃ then 1 else 0)) := by
  have hcard : ((Finset.univ.filter (fun a : K =>
      (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ) ≤ Fintype.card K := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset
      (fun a : K => (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄)) Finset.univ)
  have hp : (0 : ℝ) ≤ Fintype.card K := Nat.cast_nonneg _
  by_cases h₁ : b₁ = b₃ ∧ b₂ = b₄
  · by_cases h₂ : b₁ = b₄ ∧ b₂ = b₃
    · rw [ite_eq_left h₁, ite_eq_left h₂]
      linarith
    · rw [ite_eq_left h₁, ite_eq_right h₂]
      linarith
  · by_cases h₂ : b₁ = b₄ ∧ b₂ = b₃
    · rw [ite_eq_right h₁, ite_eq_left h₂]
      linarith
    · rw [ite_eq_right h₁, ite_eq_right h₂]
      simp only [add_zero, mul_zero]
      exact_mod_cast quadraticPair_collision_card_le_one b₁ b₂ b₃ b₄
        (not_or.mpr ⟨h₁, h₂⟩)

end Ostmann

end OAI
