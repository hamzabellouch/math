import OAI.NumberTheory.Ostmann.Characters.CharacterPrimeCells
import OAI.NumberTheory.Ostmann.Characters.CharacterSelectionBudget

namespace OAI

/-! # One fixed covering error for every selected character-cell list -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterCellCoveringError (c δ : ℝ) (k : ℕ) : ℝ :=
  64 / (δ * c) + (characterTargetLabelBound c δ k : ℝ) + 1

theorem characterCellCoveringError_gt_one (c δ : ℝ) (k : ℕ) (hc : 0 < c) (hδ : 0 < δ) :
    1 < characterCellCoveringError c δ k := by
  unfold characterCellCoveringError
  have he : 0 < 64 / (δ * c) := by positivity
  have hn := Nat.cast_nonneg (α := ℝ) (characterTargetLabelBound c δ k)
  linarith

theorem character_selected_cell_size_le {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) (v : CharacterCell k) :
    characterCellSize (fun j => (w (some j)).indices.length) (w none).indices.length v ≤
      characterTargetLabelBound c δ k + 1 := by
  have hlen (j : Option (Fin k)) : (w j).indices.length ≤ characterTargetLabelBound c δ k :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (character_target_label_bound w)
  rcases v with j | j | u
  · exact (hlen (some j)).trans (Nat.le_succ _)
  · exact Nat.le_add_left 1 _
  · exact (hlen none).trans (Nat.le_succ _)

/-- Neither the selected endpoint nor the number of labels creates another
range hypothesis: the explicit uniform covering error bounds every group. -/
theorem character_selected_product_intervals {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : Fin k → Bool → ℕ) (J : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    let E := characterCellCoveringError c δ k
    ∀ v : CharacterCell k,
      Real.exp (characterLogCenter J (fun j => T (some j)) (fun j b => (a j b : ℝ))
        (T none) (true, some v) - E) ≤
        (∏ i, primeCellLower (characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i) : ℕ) ∧
      (∏ i, primeCellUpper (characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i) : ℕ) ≤
        Real.exp (characterLogCenter J (fun j => T (some j)) (fun j b => (a j b : ℝ))
          (T none) (true, some v) + E) := by
  intro E
  apply characterPrimeCells_product_bounds w a J E hc hδ
  intro v
  have hv : (characterCellSize (fun j => (w (some j)).indices.length) (w none).indices.length v : ℝ) ≤
      (characterTargetLabelBound c δ k : ℝ) + 1 := by
    exact_mod_cast character_selected_cell_size_le w v
  change 64 / (δ * c) + _ ≤ 64 / (δ * c) + (characterTargetLabelBound c δ k : ℝ) + 1
  linarith

end Ostmann

end OAI
