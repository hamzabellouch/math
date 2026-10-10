import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduleRanges
import OAI.NumberTheory.Ostmann.Construction.WordRangePolynomial

namespace OAI

/-! # The original atom ranges are exactly the replayed prime-word tests -/

namespace Ostmann

open scoped Classical

theorem expanded_schedule_pivot_eq {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ)
    (childBound pivotBound : ℕ → ℕ) (n : ℕ) (path : List Bool)
    (current : CopyScheduleAtoms role (n + 1) → List σ) (x : σ → ℕ) (s v w : ℤ) :
    historyPivot (wordTransferSystem σ)
      ((expandedScheduledTemplate role address childBound pivotBound (n + 1) path current).state x) s v w =
    historyPivot (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, expandedAtomValues role (n + 1) current x⟩ s v w := by
  simp only [historyPivot, expandedScheduledTemplate, WordTransferTemplate.state,
    wordTransferSystem, wordTransferLeft, wordTransferRight, expandedHWord_product,
    scheduleAtomSystem, scheduleAtomLeft, scheduleAtomRight, expandedAtomValues]

noncomputable def scheduleAtomRangesValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n)) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, x, _ => ∀ r ∈ ranges 0, r.Holds x
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ r ∈ ranges (n + 1), r.Holds x) ∧
        scheduleAtomRangesValid role childBound pivotBound ranges n (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomRangesValid role childBound pivotBound ranges n (reverseCopyLabelMap role n false P x) t.2.2

theorem expandedScheduleRanges_valid_iff {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    (expandedScheduleRanges role (expandedPivotAddress α depth) ranges n path current).ValidAt
        (expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound n path current) x t ↔
      scheduleAtomRangesValid role childBound pivotBound ranges n (expandedAtomValues role n current x) t := by
  induction n generalizing path x with
  | zero =>
    simp only [expandedScheduleRanges, expandedScheduledTemplate, WordRangeDecoration.ValidAt,
      scheduleAtomRangesValid, List.forall_mem_map]
    exact forall₂_congr fun r _ => r.toWord_holds current x
  | succ n ih =>
    let P := historyPivot (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, expandedAtomValues role (n + 1) current x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    have hn' : n ≤ depth := by omega
    have hL := ih hn' (true :: path)
      (reverseCopyLabelMap role n true [expandedPivotAddress α depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' true path current hc)
      (Function.update x (expandedPivotAddress α depth n path) P) t.2.1
    have hR := ih hn' (false :: path)
      (reverseCopyLabelMap role n false [expandedPivotAddress α depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' false path current hc)
      (Function.update x (expandedPivotAddress α depth n path) P) t.2.2
    rw [expanded_schedule_child_state role depth n hn' true path current hc x P] at hL
    rw [expanded_schedule_child_state role depth n hn' false path current hc x P] at hR
    have hp := expanded_schedule_pivot_eq role (expandedPivotAddress α depth)
      childBound pivotBound n path current x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    dsimp only [expandedScheduledTemplate] at hp
    simp only [expandedScheduleRanges, expandedScheduledTemplate, WordRangeDecoration.ValidAt,
      hp, scheduleAtomRangesValid, List.forall_mem_map]
    apply and_congr (forall₂_congr fun r _ => r.toWord_holds current x)
    apply and_congr
    · convert hL using 2
      congr 2
      exact Subsingleton.elim _ _
    · convert hR using 2
      congr 2
      exact Subsingleton.elim _ _

end Ostmann

end OAI
