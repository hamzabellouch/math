import OAI.NumberTheory.Ostmann.Construction.ConstructedCharacterCells
import OAI.NumberTheory.Ostmann.Characters.CharacterSelectionRate

namespace OAI

/-! # Common normalized character priors for exponentially many endpoints -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Fixing the actual anchor and whole-shell codes leaves a single collection
of harmonic probability laws. Every retained endpoint has a large mean under
these same laws, with the explicit selection cost from the code count. -/
theorem eventual_fixed_character_priors (c δ β C z : ℝ) (k : ℕ)
    (hc : 0 < c) (hδ : 0 < δ) (hC : 0 ≤ C) (hz : 1 ≤ z)
    (hsize : ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (m X A U : ℝ),
      (B + 1 : ℕ) ≤ Real.exp (C * L) → z * L ≤ 2 * m → U ≤ β * L →
      ∀ (E : Finset ℕ), E.Nonempty → Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∀ (P : Finset ℕ) (G : ℕ → ℕ → ℂ) (ζ : ℂ), ‖ζ‖ = 1 →
      5 * k ≤ B → (∀ p ∈ P, primeLogIndex p ≤ B) →
      ∀ (u : Fin k × Bool → ℝ), (∀ j, u j ≤ β * L) →
      ∀ (a : ∀ x j, CharacterAnchorCell P (fun p => ζ * G x p) c δ (u j)),
      (∀ x ∈ E, ∀ j, (a x j).index ≤ B) →
      ∀ (T : ℕ → Option (Fin k) → ℝ)
        (w : ∀ x j, CharacterTargetWord P (fun p => ζ * G x p) c δ U k (T x j)),
      ∃ x₀ ∈ E, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells (w x₀) (characterAnchorCells (a x₀))
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) := by
  filter_upwards [eventual_common_character_selection k (characterTargetLabelBound c δ k)
    C z hC hz hsize,
    eventually_ge_atTop (5 * (k : ℝ) - Real.log (δ * c / 32))] with L hselect hL
  intro B m X A U hB hm hU E hE hEcard P G ζ hζ hk hP u hu a ha T w
  obtain ⟨x₀, hx₀, S, hSE, hS, hScard, hdata⟩ := hselect B m X A hB hm E hE hEcard
    P (fun x p => ζ * G x p) c δ U (fun x j => (a x j).index) T w hc hδ hk hP ha
    (fun x _ => character_target_label_bound (w x))
  refine ⟨x₀, hx₀, S, hSE, hS, hScard, ?_⟩
  dsimp only
  refine ⟨characterPrimeCells_subset (w x₀) (characterAnchorCells (a x₀))
    (fun j => (a x₀ j).cell_subset),
    constructed_character_cells_probability (w x₀) (a x₀) hc hδ,
    constructed_character_cells_mass (w x₀) (a x₀) hc hδ β L hU hu hL, ?_⟩
  intro x hx
  apply constructed_character_cells_endpoint_mean (w x₀) (a x₀) ζ hζ (w x) (a x)
    (hdata x hx).2
  intro j
  exact congrFun (hdata x hx).1 j

end Ostmann

end OAI
