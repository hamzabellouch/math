import OAI.Combinatorics.MatrixRemoval.CanonicalModeEntries
import OAI.Combinatorics.MatrixRemoval.ModeLocalization

namespace OAI

/-! Horizontal body localization for the canonical host entry table. -/
namespace Problem348.Construction
open ModeLocalization

theorem horizontal_plus_entries_impossible {h i : ℕ} {r c₀ c₁ : VariablePosition h}
    (hr : AtLevel (i + 1) true r) (hc₀ : AtLevel i true c₀)
    (hc₁ : AtLevel (i + 1) true c₁)
    (horder : node c₀ ≤ node c₁ / 2) (hparity : node r % 2 = node c₁ % 2)
    (h₀ : variableEntry r c₀ = true) (h₁ : variableEntry r c₁ = false) : False := by
  apply wPlus_not_isP (node r) (node c₁) (node c₀) horder hparity
  exact ⟨by simpa only [variableEntry_child_parent_plus hr hc₀] using h₀,
    by simpa only [variableEntry_same_plus hr hc₁] using h₁, rfl, rfl⟩

/-- A W- body forces the shared leaf diagonal, as literal variable positions. -/
theorem horizontal_minus_entries_localize {h i : ℕ} {r c₀ c₁ : VariablePosition h}
    (hr : AtLevel (i + 1) false r) (hc₀ : AtLevel (i + 1) false c₀)
    (hc₁ : AtLevel i false c₁)
    (horder : node c₀ / 2 ≤ node c₁) (hparity : node r % 2 = node c₀ % 2)
    (h₀ : variableEntry r c₀ = true) (h₁ : variableEntry r c₁ = false) :
    i + 1 = h ∧ ∃ z : Fin (2 ^ h),
      r = (Fin.last (2 * h), z) ∧ c₀ = (Fin.last (2 * h), z) := by
  have hb : IsP
      (if i + 1 = h then decide (node r ≤ node c₀) else decide (node r < node c₀))
      (decide (node r / 2 < node c₁)) true true := by
    exact ⟨by simpa only [variableEntry_same_minus hr hc₀] using h₀,
      by simpa only [variableEntry_child_parent_minus hr hc₁] using h₁, rfl, rfl⟩
  obtain ⟨hi, heq⟩ := wMinus_isP_implies_leaf_diagonal h (i + 1) (node r) (node c₀) (node c₁) horder hparity hb
  have hrd : depth r = h := hr.1.trans hi
  have hcd : depth c₀ = h := hc₀.1.trans hi
  have hz : r.2 = c₀.2 := by
    apply Fin.ext
    simpa only [node_eq_index_of_depth_eq hrd, node_eq_index_of_depth_eq hcd] using heq
  exact ⟨hi, r.2, eq_leaf_of_depth_eq hrd, by simpa only [hz] using eq_leaf_of_depth_eq hcd⟩

end Problem348.Construction

end OAI
