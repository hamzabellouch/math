import OAI.NumberTheory.Ostmann.Construction.ScheduleAtomSystem

namespace OAI

/-! # The prime-word and atom systems have identical valid histories -/

namespace Ostmann

open scoped Classical

theorem expanded_schedule_history_iff {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    ValidTransferHistory (wordTransferSystem (ExpandedScheduledVariable α depth)) n
      ((expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound n path current).state x) t ↔
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, expandedAtomValues role n current x⟩ t := by
  induction n generalizing path x with
  | zero => trivial
  | succ n ih =>
    have hn' : n ≤ depth := by omega
    change (∃ P, ValidTransferNode _ _ _ _ _ P ∧ _ ∧ _) ↔
      (∃ P, ValidTransferNode _ _ _ _ _ P ∧ _ ∧ _)
    apply exists_congr
    intro P
    apply and_congr (expanded_schedule_node_iff role (expandedPivotAddress α depth)
      childBound pivotBound n path current x _ _ _ P)
    apply and_congr
    · have he := expanded_schedule_child_state role depth n hn' true path current hc x P
      have hh := ih hn' (true :: path)
        (reverseCopyLabelMap role n true [expandedPivotAddress α depth n path] current)
        (reverseExpandedCoordinates_after role depth n hn' true path current hc)
        (Function.update x (expandedPivotAddress α depth n path) P) t.2.1
      rw [he] at hh
      rw [expandedScheduledTemplate, wordTransferLeftState_node]
      exact hh
    · have he := expanded_schedule_child_state role depth n hn' false path current hc x P
      have hh := ih hn' (false :: path)
        (reverseCopyLabelMap role n false [expandedPivotAddress α depth n path] current)
        (reverseExpandedCoordinates_after role depth n hn' false path current hc)
        (Function.update x (expandedPivotAddress α depth n path) P) t.2.2
      rw [he] at hh
      rw [expandedScheduledTemplate, wordTransferRightState_node]
      exact hh

/-- All initial constituent primes feed the actual atom products; the
constructed finite coordinates impose no extra validity conditions. -/
theorem expandedRootTemplate_history_iff {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth : ℕ) (words : CopyScheduleAtoms role depth → List α)
    (childBound pivotBound : ℕ → ℕ) (x : ExpandedScheduledVariable α depth → ℕ)
    (t : FrequencyTree ℤ depth) :
    ValidTransferHistory (wordTransferSystem (ExpandedScheduledVariable α depth)) depth
      ((expandedRootTemplate role depth words childBound pivotBound).state x) t ↔
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) depth
      ⟨depth, fun i => (((words i).map Sum.inl).map x).prod⟩ t :=
  expanded_schedule_history_iff role childBound pivotBound depth depth le_rfl []
    (fun i => (words i).map Sum.inl) (expandedRootCoordinates_after role depth words) x t

end Ostmann

end OAI
