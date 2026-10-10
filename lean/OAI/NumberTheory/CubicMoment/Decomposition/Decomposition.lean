import Mathlib

namespace OAI

/-!
# Exact coefficient separation

Finite-set versions of the two algebraic identities used in the prime-decomposition section of
*An unconditional first moment for cubic Gauss sums* (25 September 2026):
the distinguished-factor expansion and the normalization at the stopping bin.
Elements of `s` label distinct prime ideals, including conjugate ideals of
equal norm. Thus no identification of factors with their norms is made.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

/-- Expanding the difference of two prime cutoffs independently at every
factor. This is the unordered-subset form of `eq:distinguished-tuples`. -/
theorem distinguished_factor_expansion {α : Type*} [DecidableEq α] (s : Finset α)
    (small large : α → ℂ) :
    (∏ p ∈ s, (1 - large p)) =
      ∑ t ∈ s.powerset,
        (∏ p ∈ t, (small p - large p)) * ∏ p ∈ s \ t, (1 - small p) := by
  classical
  convert Finset.prod_add (fun p => small p - large p) (fun p => 1 - small p) s
      using 1
  apply Finset.prod_congr rfl
  intro p _
  ring

/-- The same expansion collected by the number of distinguished factors. -/
theorem distinguished_factor_expansion_by_card {α : Type*} [DecidableEq α] (s : Finset α)
    (small large : α → ℂ) :
    (∏ p ∈ s, (1 - large p)) =
      ∑ k ∈ Finset.range (s.card + 1), ∑ t ∈ s.powersetCard k,
        (∏ p ∈ t, (small p - large p)) * ∏ p ∈ s \ t, (1 - small p) := by
  rw [distinguished_factor_expansion, Finset.sum_powerset]

/-- A squarefree Möbius expansion, with factors labelled before taking
their product. This gives `eq:rough-mobius-expansion`. -/
theorem rough_factor_expansion {α : Type*} (s : Finset α) (cutoff : α → ℂ) :
    (∏ p ∈ s, (1 - cutoff p)) =
      ∑ t ∈ s.powerset, (-1 : ℂ) ^ t.card * ∏ p ∈ t, cutoff p := by
  have h := Finset.prod_one_add (f := fun p => -cutoff p) s
  simpa only [sub_eq_add_neg, Finset.prod_neg] using h

/-- Each choice at a fixed stopping bin has the same multiplicative
coefficient, since its selected and unselected factors partition the bin. -/
theorem stopping_coefficient_split {α : Type*} [DecidableEq α]
    (s t : Finset α) (ht : t ⊆ s) (weight : α → ℂ) :
    (∏ p ∈ t, weight p) * (∏ p ∈ s \ t, weight p) =
      ∏ p ∈ s, weight p := by
  rw [mul_comm]
  exact Finset.prod_sdiff ht

/-- The reciprocal binomial coefficient is well-defined for every possible
count in the final bin. -/
theorem stopping_binomial_ne_zero (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.choose_pos hk).ne'

/-- The weights assigned to all possible selections in the stopping bin
sum to one. This is precisely the scalar in `eq:stopping-scalar`. -/
theorem stopping_bin_weights_sum {α : Type*} (s : Finset α)
    (k : ℕ) (hk : k ≤ s.card) :
    (∑ _t ∈ s.powersetCard k, (s.card.choose k : ℂ)⁻¹) = 1 := by
  simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  exact mul_inv_cancel₀ (stopping_binomial_ne_zero _ _ hk)

/-- Distributing a squarefree coefficient over all choices in the final
bin and dividing by their count restores the original coefficient exactly.
This is valid for arbitrary complex prime weights, without estimates. -/
theorem stopping_bin_coefficient_identity {α : Type*} [DecidableEq α]
    (s : Finset α) (k : ℕ) (hk : k ≤ s.card) (weight : α → ℂ) :
    (∑ t ∈ s.powersetCard k,
      (s.card.choose k : ℂ)⁻¹ *
        ((∏ p ∈ t, weight p) * ∏ p ∈ s \ t, weight p)) =
      ∏ p ∈ s, weight p := by
  calc
    _ = ∑ _t ∈ s.powersetCard k,
        (s.card.choose k : ℂ)⁻¹ * ∏ p ∈ s, weight p := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [stopping_coefficient_split s t (Finset.mem_powersetCard.mp ht).1]
    _ = (∑ _t ∈ s.powersetCard k, (s.card.choose k : ℂ)⁻¹) *
        ∏ p ∈ s, weight p := (Finset.sum_mul ..).symm
    _ = _ := by rw [stopping_bin_weights_sum s k hk, one_mul]

/-- The crossing test only uses the common bin endpoint and the selected
count, so it is identical for every selection having that count. -/
theorem stopping_crossing_independent {α : Type*} (s : Finset α) (k : ℕ)
    (r ell threshold : ℝ) (t : Finset α) (ht : t ∈ s.powersetCard k) :
    (r * ell ^ t.card / ell < threshold ∧ threshold ≤ r * ell ^ t.card) ↔
      (r * ell ^ k / ell < threshold ∧ threshold ≤ r * ell ^ k) := by
  rw [(Finset.mem_powersetCard.mp ht).2]

end CubicFirstMoment

end

end OAI
