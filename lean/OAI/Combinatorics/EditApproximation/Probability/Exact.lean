import OAI.Combinatorics.EditApproximation.Geometry.AlignmentSplitting
import OAI.Combinatorics.EditApproximation.Geometry.Leaves

namespace OAI

/-!
# An executable exact cut recurrence

This is the exact source-cut dynamic programming recurrence on ordinary
lists and natural numbers. The proof identifies its value with unrestricted
unit-cost edit distance. Storage and evaluation costs are separate from
this value-level recurrence.
-/

namespace EditApproximation

open EditDistortion

def finiteNatMinimum (fallback : ℕ) : List ℕ → ℕ
  | [] => fallback
  | value :: rest => min value (finiteNatMinimum fallback rest)

theorem le_finiteNatMinimum_iff (lower fallback : ℕ) (values : List ℕ) :
    lower ≤ finiteNatMinimum fallback values ↔
      lower ≤ fallback ∧ ∀ value ∈ values, lower ≤ value := by
  induction values with
  | nil => simp [finiteNatMinimum]
  | cons value rest ih =>
    simp only [finiteNatMinimum, le_min_iff, ih, List.mem_cons, forall_eq_or_imp]
    tauto

theorem finiteNatMinimum_le_member (fallback : ℕ) (values : List ℕ)
    {value : ℕ} (hvalue : value ∈ values) : finiteNatMinimum fallback values ≤ value := by
  induction values with
  | nil => simp at hvalue
  | cons first rest ih =>
    rcases List.mem_cons.mp hvalue with rfl | hvalue
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hvalue)

def exactCutCost {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | [], target => target.length
  | a :: rest, target => finiteNatMinimum (rest.length + 1 + target.length)
      ((List.range (target.length + 1)).map fun cut =>
        singletonCost a (target.take cut) + exactCutCost rest (target.drop cut))

theorem edit_nil_left {α : Type*} (target : List α) : edit [] target = target.length := by
  have hlo := (cost_length_bounds (s := true) ([] : List α) target).2
  have hup := cost_le (Script.to_nil (s := true) target).symm
  change edit [] target ≤ target.length at hup
  change target.length ≤ 0 + edit [] target at hlo
  omega

theorem exactCutCost_eq_edit {α : Type*} [DecidableEq α] (source target : List α) :
    exactCutCost source target = edit source target := by
  induction source generalizing target with
  | nil => exact (edit_nil_left target).symm
  | cons a rest ih =>
    have hcandidate (cut : ℕ) : edit (a :: rest) target ≤
        singletonCost a (target.take cut) + exactCutCost rest (target.drop cut) := by
      rw [singletonCost_eq_edit, ih]
      have happend := cost_append_le (s := true) [a] (target.take cut) rest (target.drop cut)
      simpa only [List.singleton_append, List.take_append_drop, cost, edit] using happend
    apply Nat.le_antisymm
    · obtain ⟨tl, tr, ht, hc⟩ := edit_append_split [a] rest target
      let cut := tl.length
      have hcut : cut < target.length + 1 := by simp only [ht, List.length_append]; omega
      have htake : target.take cut = tl := by simp [ht, cut]
      have hdrop : target.drop cut = tr := by simp [ht, cut]
      have hmin := finiteNatMinimum_le_member (rest.length + 1 + target.length)
        ((List.range (target.length + 1)).map fun j =>
          singletonCost a (target.take j) + exactCutCost rest (target.drop j))
        (List.mem_map.mpr ⟨cut, List.mem_range.mpr hcut, rfl⟩)
      change exactCutCost (a :: rest) target ≤
        singletonCost a (target.take cut) + exactCutCost rest (target.drop cut) at hmin
      rw [htake, hdrop, singletonCost_eq_edit, ih] at hmin
      simpa only [List.singleton_append] using hmin.trans_eq hc.symm
    · apply (le_finiteNatMinimum_iff _ _ _).2
      constructor
      · have hup := edit_le_total_length (a :: rest) target
        simpa only [List.length_cons, Nat.add_assoc] using hup
      · intro value hvalue
        obtain ⟨cut, _, rfl⟩ := List.mem_map.mp hvalue
        exact hcandidate cut

end EditApproximation

end OAI
