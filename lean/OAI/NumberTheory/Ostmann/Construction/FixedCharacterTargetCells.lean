import OAI.NumberTheory.Ostmann.Characters.CharacterTargetCode
import OAI.NumberTheory.Ostmann.Characters.CharacterMeanRotation

namespace OAI

/-! # The fixed target-cell priors after the endpoint pigeonhole -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def fixedTargetCells {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (i : Σ j, Fin (w j).indices.length) : Finset ℕ :=
  (w i.1).cell ((w i.1).indices.get i.2)

theorem fixedTargetCells_subset {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (i : Σ j, Fin (w j).indices.length) : fixedTargetCells w i ⊆ P :=
  (w i.1).cell_subset _

theorem fixedTargetCells_mass {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) (hc : 0 < c) (hδ : 0 < δ)
    (β L : ℝ) (hU : U ≤ β * L) (hL : 5 * (k : ℝ) - Real.log (δ * c / 32) ≤ L)
    (i : Σ j, Fin (w j).indices.length) :
    Real.exp (-(β + 1) * L) ≤ ∑ p ∈ fixedTargetCells w i, (p : ℝ)⁻¹ :=
  (w i.1).cell_mass_exponential hc hδ β L hU hL _ (List.get_mem _ _)

/-- Identical shell/list data preserves the positive norm at every retained
endpoint, although its test function and target certificate may differ. -/
theorem fixedTargetCells_unrotated_mean {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (v : ∀ j, CharacterTargetWord P (fun p => ζ * G p) c δ U k (S j))
    (hdata : ∀ j, (v j).indices = (w j).indices ∧
      ∀ h, (v j).cell h = (w j).cell h)
    (i : Σ j, Fin (w j).indices.length) :
    δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P (fixedTargetCells w i) p : ℂ) * G p‖ := by
  have hmem : (w i.1).indices.get i.2 ∈ (v i.1).indices := by
    rw [(hdata i.1).1]
    exact List.get_mem _ _
  have hm := (v i.1).cell_unrotated_mean ζ hζ _ hmem
  rw [(hdata i.1).2] at hm
  exact hm

theorem fixedTargetCells_product_bounds {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) (E : ℝ)
    (hE : ∀ j, 64 / (δ * c) + (w j).indices.length ≤ E) (j : Option (Fin k)) :
    Real.exp (T j - E) ≤
      (∏ i : Fin (w j).indices.length, primeCellLower ((w j).indices.get i) : ℕ) ∧
    (∏ i : Fin (w j).indices.length, primeCellUpper ((w j).indices.get i) : ℕ) ≤
      Real.exp (T j + E) :=
  list_primeCell_target_products (w j).indices (T j) (64 / (δ * c)) E (w j).error.le (hE j)

end Ostmann

end OAI
