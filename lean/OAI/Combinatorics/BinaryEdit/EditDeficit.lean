import OAI.Combinatorics.BinaryEdit.LCSEditUpper
import OAI.Combinatorics.BinaryEdit.EditLCSLower

namespace OAI

/-!
Both metric comparisons in the preliminary section, for the actual unrestricted
unit-cost edit scripts and longest-common-subsequence definitions.
-/
namespace TreeEdit.BinaryLower

/-- Second inequality of source equation `eq:metric-conversion`. -/
theorem delta_le_twice_editDistance {α : Type*} (x y : List α) :
    x.length + y.length - 2 * lcs x y ≤ 2 * ed x y := by
  have hs : EditScript x y (ed x y) :=
    TreeEdit.ed_script x y
  exact EditScript.lcs_loss_le hs

/-- Ordinary edit distance and insertion--deletion distance differ by at most
factor two, without imposing a cap on intermediate script words. -/
theorem editDistance_delta_bounds {α : Type*} (x y : List α) :
    ed x y ≤ x.length + y.length - 2 * lcs x y ∧
      x.length + y.length - 2 * lcs x y ≤ 2 * ed x y :=
  ⟨editDistance_le_delta x y, delta_le_twice_editDistance x y⟩

/-- Lower inequality of source equation `eq:deficit`, on equal-length words. -/
theorem deficit_le_editDistance {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    deficit n x y ≤ ed x y := by
  have h := delta_le_twice_editDistance x y
  rw [hx, hy] at h
  unfold deficit
  omega

/-- The complete equal-length deficit comparison, including empty words. -/
theorem editDistance_deficit_bounds {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    deficit n x y ≤ ed x y ∧
      ed x y ≤ 2 * deficit n x y :=
  ⟨deficit_le_editDistance hx hy, editDistance_le_twice_deficit hx hy⟩

/-- Real-valued form used in the fixed-length binary conversion inequalities. -/
theorem editDistance_deficit_bounds_real {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    (deficit n x y : ℝ) ≤ (ed x y : ℝ) ∧
      (ed x y : ℝ) ≤ 2 * (deficit n x y : ℝ) := by
  constructor
  · exact_mod_cast deficit_le_editDistance hx hy
  · exact_mod_cast editDistance_le_twice_deficit hx hy

end TreeEdit.BinaryLower

end OAI
