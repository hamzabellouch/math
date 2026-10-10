import OAI.Combinatorics.Progressions.Estimates.StrideProductBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem booleanBlockPhase_major_arc {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin (n+1) → ℕ) (u : Fin (n+1) → Option α → ℝ) (ξ : Finset α → ℝ)
    (J : Finset (Finset α)) (hJ : ∀ S ∈ J, S.card ≤ n+1) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hbias : ζ ≤ ‖𝔼 x : ∀ g, Option α → Fin (N g),
      character ((booleanBlockPhase ξ (fun g r => u g r+((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (multiaffineBiasBudget n ζ)^J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S-(a S : ℝ)/D| ≤
        multiaffineBiasBudget n ζ / ∏ g, (N g : ℝ) := by
  have h := exists_common_rational_approximations (fun S : J => ξ S)
    (fun S => booleanBlockPhase_entry_approximation N u ξ S (hJ S S.property) hζ hN hbias)
  simpa only [Fintype.card_coe] using h

theorem booleanBlockPhase_minor_arc {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin (n+1) → ℕ) (u : Fin (n+1) → Option α → ℝ) (ξ : Finset α → ℝ)
    (J : Finset (Finset α)) (hJ : ∀ S ∈ J, S.card ≤ n+1) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hminor : ∀ D : ℕ, 0 < D → (D : ℝ) ≤ (multiaffineBiasBudget n ζ)^J.card →
      ∀ a : J → ℤ, ∃ S : J, multiaffineBiasBudget n ζ / ∏ g, (N g : ℝ) <
        |ξ S-(a S : ℝ)/D|) :
    ‖𝔼 x : ∀ g, Option α → Fin (N g),
      character ((booleanBlockPhase ξ (fun g r => u g r+((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖ < ζ := by
  by_contra h
  obtain ⟨D,hD,hDQ,a,ha⟩ := booleanBlockPhase_major_arc N u ξ J hJ hζ hN (le_of_not_gt h)
  obtain ⟨S,hS⟩ := hminor D hD hDQ a
  exact (not_lt_of_ge (ha S)) hS

end Erdos3

end

end OAI
