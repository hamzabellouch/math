import OAI.NumberTheory.Ostmann.Construction.FixedCharacterTargetCells
import OAI.NumberTheory.Ostmann.Characters.CharacterCellIntervals

namespace OAI

/-! # The actual pivot, anchor and filler marginals on the common prime set -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterPrimeCells {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) (A : Fin k × Bool → Finset ℕ) :
    (v : CharacterCell k) →
      Fin (characterCellSize (fun j => (w (some j)).indices.length) (w none).indices.length v) → Finset ℕ
  | .inl j, i => fixedTargetCells w ⟨some j, i⟩
  | .inr (.inl j), _ => A j
  | .inr (.inr _), i => fixedTargetCells w ⟨none, i⟩

theorem characterPrimeCells_subset {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) (A : Fin k × Bool → Finset ℕ)
    (hA : ∀ j, A j ⊆ P) : ∀ v i, characterPrimeCells w A v i ⊆ P := by
  rintro (j | (j | u)) i
  · exact fixedTargetCells_subset w ⟨some j, i⟩
  · exact hA j
  · exact fixedTargetCells_subset w ⟨none, i⟩

theorem characterPrimeCells_norm_mean {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (A : Fin k × Bool → Finset ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (v : ∀ j, CharacterTargetWord P (fun p => ζ * G p) c δ U k (S j))
    (hdata : ∀ j, (v j).indices = (w j).indices ∧ ∀ h, (v j).cell h = (w j).cell h)
    (hA : ∀ j, δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P (A j) p : ℂ) * G p‖) :
    ∀ a i, δ / 2 ≤
      ‖∑ p : P, (primeSubsetPrior P (characterPrimeCells w A a i) p : ℂ) * G p‖ := by
  rintro (j | (j | u)) i
  · exact fixedTargetCells_unrotated_mean w ζ hζ v hdata ⟨some j, i⟩
  · exact hA j
  · exact fixedTargetCells_unrotated_mean w ζ hζ v hdata ⟨none, i⟩

theorem characterPrimeCells_index {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (A : Fin k × Bool → Finset ℕ) (a : Fin k → Bool → ℕ)
    (hA : ∀ j b p, p ∈ A (j, b) → primeLogIndex p = a j b) :
    ∀ v i p, p ∈ characterPrimeCells w A v i →
      primeLogIndex p = characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i := by
  rintro (j | (⟨j, b⟩ | u)) i p hp
  · exact (Finset.mem_filter.mp hp).2
  · exact hA j b p hp
  · exact (Finset.mem_filter.mp hp).2

/-- The target certificate gives the whole-atom endpoints used by the
initial amplitude and all later transfer steps. -/
theorem characterPrimeCells_product_bounds {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : Fin k → Bool → ℕ) (J E : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hE : ∀ v, 64 / (δ * c) +
      (characterCellSize (fun j => (w (some j)).indices.length) (w none).indices.length v : ℝ) ≤ E) :
    ∀ v : CharacterCell k,
      Real.exp (characterLogCenter J (fun j => T (some j)) (fun j b => (a j b : ℝ))
        (T none) (true, some v) - E) ≤
        (∏ i, primeCellLower (characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i) : ℕ) ∧
      (∏ i, primeCellUpper (characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i) : ℕ) ≤
        Real.exp (characterLogCenter J (fun j => T (some j)) (fun j b => (a j b : ℝ))
          (T none) (true, some v) + E) := by
  exact characterCellIndex_product_bounds (fun j => (w (some j)).indices) a (w none).indices
    J (T none) (64 / (δ * c)) E (fun j => T (some j)) (by positivity)
    (fun j => (w (some j)).error.le) (w none).error.le hE

end Ostmann

end OAI
