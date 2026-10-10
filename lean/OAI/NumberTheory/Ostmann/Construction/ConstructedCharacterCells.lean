import OAI.NumberTheory.Ostmann.Characters.CharacterAnchorCells
import OAI.NumberTheory.Ostmann.Characters.CharacterCellCovering

namespace OAI

/-! # The selected pivot, filler and anchor cells form actual probability laws -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterAnchorCells {P : Finset ℕ} {F : ℕ → ℂ} {c δ : ℝ}
    {k : ℕ} {u : Fin k × Bool → ℝ}
    (a : ∀ j, CharacterAnchorCell P F c δ (u j)) : Fin k × Bool → Finset ℕ :=
  fun j => (a j).cell

theorem constructed_character_cells_mass {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j))
    (hc : 0 < c) (hδ : 0 < δ) (β L : ℝ) (hU : U ≤ β * L)
    (hu : ∀ j, u j ≤ β * L) (hL : 5 * (k : ℝ) - Real.log (δ * c / 32) ≤ L) :
    ∀ v i, Real.exp (-(β + 1) * L) ≤
      ∑ p ∈ characterPrimeCells w (characterAnchorCells a) v i, (p : ℝ)⁻¹ := by
  rintro (j | (j | v)) i
  · exact fixedTargetCells_mass w hc hδ β L hU hL ⟨some j, i⟩
  · apply (a j).cell_mass_exponential hc hδ β L (hu j)
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith
  · exact fixedTargetCells_mass w hc hδ β L hU hL ⟨none, i⟩

theorem constructed_character_cells_probability {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j))
    (hc : 0 < c) (hδ : 0 < δ) :
    ∀ v i, ∑ p : P, primeSubsetPrior P
      (characterPrimeCells w (characterAnchorCells a) v i) p = 1 := by
  intro v i
  apply primeSubsetPrior_mass
  · exact characterPrimeCells_subset w (characterAnchorCells a) (fun j => (a j).cell_subset) v i
  · rcases v with j | j | v
    · exact ((by positivity : 0 < δ * c / (32 * Real.exp (U + (w (some j)).shell))).trans_le
        ((w (some j)).cell_mass _ (List.get_mem _ _))).ne'
    · exact ((a j).cell_mass_pos hc hδ).ne'
    · exact ((by positivity : 0 < δ * c / (32 * Real.exp (U + (w none).shell))).trans_le
        ((w none).cell_mass _ (List.get_mem _ _))).ne'

theorem constructed_character_cells_endpoint_mean {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j))
    (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (v : ∀ j, CharacterTargetWord P (fun p => ζ * G p) c δ U k (S j))
    (b : ∀ j, CharacterAnchorCell P (fun p => ζ * G p) c δ (u j))
    (hdata : ∀ j, (v j).indices = (w j).indices ∧ ∀ h, (v j).cell h = (w j).cell h)
    (hanchor : ∀ j, (b j).index = (a j).index) :
    ∀ j i, δ / 2 ≤ ‖∑ p : P,
      (primeSubsetPrior P (characterPrimeCells w (characterAnchorCells a) j i) p : ℂ) * G p‖ := by
  apply characterPrimeCells_norm_mean w (characterAnchorCells a) ζ hζ v hdata
  intro j
  have h := (b j).unrotated_mean ζ hζ
  rw [(b j).cell_eq_of_index (a j) (hanchor j)] at h
  exact h

theorem constructed_character_cells_prime_bounds {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j)) (hP : ∀ p ∈ P, p.Prime) :
    ∀ v i p, p ∈ characterPrimeCells w (characterAnchorCells a) v i →
      let h := characterCellIndex (fun j => (w (some j)).indices)
        (fun j b => (a (j, b)).index) (w none).indices v i
      primeCellLower h ≤ p ∧ p ≤ primeCellUpper h := by
  intro v i p hp
  apply primeCell_interval p _
    (hP p (characterPrimeCells_subset w (characterAnchorCells a)
      (fun j => (a j).cell_subset) v i hp))
  exact characterPrimeCells_index w (characterAnchorCells a) (fun j b => (a (j, b)).index)
    (fun _ _ _ h => (Finset.mem_filter.mp h).2) v i p hp

end Ostmann

end OAI
