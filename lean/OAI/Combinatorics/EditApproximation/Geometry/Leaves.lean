import OAI.Combinatorics.EditApproximation.Geometry.Geometry
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Exact interval-tree leaves

An occurrence query gives the exact unit-cost edit distance at a source
leaf of width one (Section 2 of the manuscript).
-/

namespace EditApproximation

open EditDistortion

universe u

/-- The part of the singleton cost determined by length and occurrence. -/


theorem occurrenceDeficit_le_length {α : Type u} [DecidableEq α]
    (a : α) (word : List α) : occurrenceDeficit a word ≤ word.length := Nat.sub_le _ _

theorem length_le_occurrenceDeficit_add_one {α : Type u} [DecidableEq α]
    (a : α) (word : List α) : word.length ≤ occurrenceDeficit a word + 1 := by
  unfold occurrenceDeficit
  split_ifs <;> omega

/-- One edit can increase the occurrence deficit by at most one. -/
theorem occurrenceDeficit_step {α : Type u} [DecidableEq α]
    (a : α) {x y : List α} (h : Step true x y) :
    occurrenceDeficit a y ≤ occurrenceDeficit a x + 1 := by
  cases h with
  | insert p q b =>
    by_cases ha : a ∈ p ++ q
    · have ha' : a ∈ p ++ b :: q := by
        simp only [List.mem_append, List.mem_cons] at ha ⊢
        tauto
      simp only [occurrenceDeficit, ite_eq_left ha, ite_eq_left ha',
        List.length_append, List.length_cons]
      omega
    · have hup := occurrenceDeficit_le_length a (p ++ b :: q)
      simp only [occurrenceDeficit, ite_eq_right ha, Nat.sub_zero,
        List.length_append, List.length_cons] at hup ⊢
      omega
  | delete p q b =>
    have hup := occurrenceDeficit_le_length a (p ++ q)
    have hlo := length_le_occurrenceDeficit_add_one a (p ++ b :: q)
    simp only [List.length_append, List.length_cons] at hup hlo
    omega
  | substitute _ p q b c =>
    have hup := occurrenceDeficit_le_length a (p ++ c :: q)
    have hlo := length_le_occurrenceDeficit_add_one a (p ++ b :: q)
    simp only [List.length_append, List.length_cons] at hup hlo
    omega

theorem occurrenceDeficit_script {α : Type u} [DecidableEq α]
    (a : α) {x y : List α} {n : ℕ} (h : Script true n x y) :
    occurrenceDeficit a y ≤ occurrenceDeficit a x + n := by
  induction h with
  | nil => omega
  | cons step rest ih =>
    have hs := occurrenceDeficit_step a step
    omega

theorem occurrenceDeficit_le_singleton_edit {α : Type u} [DecidableEq α]
    (a : α) (word : List α) : occurrenceDeficit a word ≤ edit [a] word := by
  have h := occurrenceDeficit_script a (cost_spec (s := true) [a] word)
  simpa [occurrenceDeficit, cost, edit] using h

/-- Executable exact answer for a source interval containing one symbol. -/


theorem singletonCost_eq_edit {α : Type u} [DecidableEq α]
    (a : α) (word : List α) : singletonCost a word = edit [a] word := by
  by_cases hempty : word = []
  · subst word
    have hlo := (cost_length_bounds (s := true) [a] []).1
    have hup := edit_le_max_length [a] ([] : List α)
    have hlo' : 1 ≤ edit [a] ([] : List α) := by
      simpa [cost, edit] using hlo
    have hup' : edit [a] ([] : List α) ≤ 1 := by simpa using hup
    simpa [singletonCost] using Nat.le_antisymm hlo' hup'
  · rw [singletonCost, ite_eq_right hempty]
    apply Nat.le_antisymm (occurrenceDeficit_le_singleton_edit a word)
    by_cases ha : a ∈ word
    · have hs : [a].Sublist word := List.singleton_sublist.mpr ha
      have hedit : edit [a] word = edit word [a] := cost_symm _ _
      rw [hedit]
      simpa only [occurrenceDeficit, ite_eq_left ha, List.length_singleton] using
        edit_sublist_le hs
    · have hlen : 1 ≤ word.length := by
        have hpos := List.length_pos_iff.mpr hempty
        omega
      have hup := edit_le_max_length [a] word
      simpa only [occurrenceDeficit, ite_eq_right ha, Nat.sub_zero,
        List.length_singleton, max_eq_right hlen] using hup

end EditApproximation

end OAI
