import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.TreeEdit.EditMetric
import Mathlib.Tactic

namespace OAI

/-! The deletion/insertion half of the source's edit--LCS comparison. -/
namespace TreeEdit.BinaryLower

/-- Ordinary edit distance is bounded by the insertion--deletion distance
computed from a longest common subsequence. -/
theorem editDistance_add_twice_lcs_le {α : Type*} (x y : List α) :
    ed x y + 2 * lcs x y ≤ x.length + y.length := by
  have hd := TreeEdit.ed_le_deficits x y
  have hx := TreeEdit.lcs_le_length_left x y
  have hy := TreeEdit.lcs_le_length_right x y
  omega

/-- First inequality of source equation `eq:metric-conversion`. -/
theorem editDistance_le_delta {α : Type*} (x y : List α) :
    ed x y ≤ x.length + y.length - 2 * lcs x y := by
  have := editDistance_add_twice_lcs_le x y
  omega

/-- Upper inequality of source equation `eq:deficit`, on equal-length words. -/
theorem editDistance_le_twice_deficit {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    ed x y ≤ 2 * deficit n x y := by
  have h := editDistance_add_twice_lcs_le x y
  rw [hx, hy] at h
  unfold deficit
  omega

end TreeEdit.BinaryLower

end OAI
