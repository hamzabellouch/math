import OAI.Combinatorics.EditDistance.Metric
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Interval-state edit geometry

The edit distance here is the repository's unrestricted unit-cost
insertion/deletion/substitution distance, not an abstract metric supplied
as a hypothesis. These are the length and endpoint bounds in Section 2.
-/

namespace EditApproximation

open EditDistortion

universe u

/-- The target substring with boundary indices `lo` and `hi`. -/


theorem substring_length {α : Type u} (word : List α) (lo hi : ℕ)
    (hhi : hi ≤ word.length) : (substring word lo hi).length = hi - lo := by
  simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left hhi]

theorem edit_sublist_le {α : Type u} {small large : List α} (h : small.Sublist large) :
    edit large small ≤ large.length - small.length :=
  cost_le (Script.of_sublist h).allow_substitution

theorem edit_drop_indices_le {α : Type u} (word : List α) (lo lo' : ℕ) :
    edit (word.drop lo) (word.drop lo') ≤ Nat.dist lo lo' := by
  rcases le_total lo lo' with h | h
  · have hs := edit_sublist_le (List.drop_sublist_drop_left word h)
    apply hs.trans
    simp only [List.length_drop, Nat.dist_eq_sub_of_le h]
    omega
  · rw [show edit (word.drop lo) (word.drop lo') =
        edit (word.drop lo') (word.drop lo) from cost_symm _ _]
    have hs := edit_sublist_le (List.drop_sublist_drop_left word h)
    apply hs.trans
    simp only [List.length_drop, Nat.dist_eq_sub_of_le_right h]
    omega

theorem edit_substring_right_le {α : Type u} (word : List α) (lo hi hi' : ℕ) :
    edit (substring word lo hi) (substring word lo hi') ≤ Nat.dist hi hi' := by
  rcases le_total hi hi' with h | h
  · have hs := edit_sublist_le ((List.take_sublist_take_left (l := word) h).drop lo)
    rw [show edit (substring word lo hi) (substring word lo hi') =
        edit (substring word lo hi') (substring word lo hi) from cost_symm _ _]
    apply hs.trans
    simp only [List.length_drop, List.length_take, Nat.dist_eq_sub_of_le h]
    omega
  · have hs := edit_sublist_le ((List.take_sublist_take_left (l := word) h).drop lo)
    apply hs.trans
    simp only [List.length_drop, List.length_take, Nat.dist_eq_sub_of_le_right h]
    omega

/-- Changing both substring endpoints costs at most their total movement,
including when the two intervals are disjoint. -/
theorem edit_substring_endpoints_le {α : Type u} (word : List α)
    (lo hi lo' hi' : ℕ) :
    edit (substring word lo hi) (substring word lo' hi') ≤
      Nat.dist lo lo' + Nat.dist hi hi' := by
  have htri := cost_triangle (s := true) (substring word lo hi)
    (substring word lo' hi) (substring word lo' hi')
  exact htri.trans (Nat.add_le_add (edit_drop_indices_le (word.take hi) lo lo')
    (edit_substring_right_le word lo' hi hi'))

theorem abs_length_gap_le_edit {α : Type u} (x y : List α) :
    |(y.length : ℝ) - x.length| ≤ (edit x y : ℝ) := by
  obtain ⟨hxy, hyx⟩ := cost_length_bounds (s := true) x y
  have hx : (x.length : ℝ) ≤ y.length + (edit x y : ℝ) := by exact_mod_cast hxy
  have hy : (y.length : ℝ) ≤ x.length + (edit x y : ℝ) := by exact_mod_cast hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual interval-state cost is 1-Lipschitz in the endpoint metric. -/
theorem interval_cost_lipschitz {α : Type u} (x y : List α)
    (lo hi lo' hi' : ℕ) :
    |(edit x (substring y lo hi) : ℝ) - edit x (substring y lo' hi')| ≤
      (Nat.dist lo lo' + Nat.dist hi hi' : ℕ) := by
  have hmove := edit_substring_endpoints_le y lo hi lo' hi'
  have hmove' : edit (substring y lo' hi') (substring y lo hi) ≤
      Nat.dist lo lo' + Nat.dist hi hi' := by
    rw [show edit (substring y lo' hi') (substring y lo hi) =
      edit (substring y lo hi) (substring y lo' hi') from cost_symm _ _]
    exact hmove
  have hleft := (cost_triangle (s := true) x (substring y lo' hi')
    (substring y lo hi)).trans (Nat.add_le_add_left hmove' _)
  have hright := (cost_triangle (s := true) x (substring y lo hi)
    (substring y lo' hi')).trans (Nat.add_le_add_left hmove _)
  have hl : (edit x (substring y lo hi) : ℝ) ≤
      edit x (substring y lo' hi') + (Nat.dist lo lo' + Nat.dist hi hi' : ℕ) := by
    exact_mod_cast hleft
  have hr : (edit x (substring y lo' hi') : ℝ) ≤
      edit x (substring y lo hi) + (Nat.dist lo lo' + Nat.dist hi hi' : ℕ) := by
    exact_mod_cast hright
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem edit_le_total_length {α : Type u} (x y : List α) :
    edit x y ≤ x.length + y.length :=
  (edit_le_max_length x y).trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

end EditApproximation

end OAI
