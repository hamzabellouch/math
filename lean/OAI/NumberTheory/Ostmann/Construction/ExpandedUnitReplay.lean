import OAI.NumberTheory.Ostmann.Construction.ExpandedRangeReplay
import OAI.NumberTheory.Ostmann.Construction.WordUnitCoefficient

namespace OAI

/-! # Original atom frequency-units on the expanded prime-word schedule -/

namespace Ostmann

open scoped Classical

theorem ScheduleAtomRange.toWord_coprime {I σ : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (current : CopyScheduleAtoms role n → List σ) (x : σ → ℕ) (m : ℕ) :
    (((r.toWord current).word.map x).prod).Coprime m ↔
      ((r.atoms.map (expandedAtomValues role n current x)).prod).Coprime m := by
  change (((r.atoms.flatMap current).map x).prod).Coprime m ↔ _
  rw [list_flatMap_product]
  rfl

noncomputable def scheduleAtomUnitsValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n)) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, x, v => ∀ r ∈ ranges 0, ((r.atoms.map x).prod).Coprime v.natAbs
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ r ∈ ranges (n + 1), ((r.atoms.map x).prod).Coprime t.1.natAbs) ∧
        scheduleAtomUnitsValid role childBound pivotBound ranges n (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomUnitsValid role childBound pivotBound ranges n (reverseCopyLabelMap role n false P x) t.2.2

theorem expandedScheduleUnits_valid_iff {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    (expandedScheduleRanges role (expandedPivotAddress α depth) ranges n path current).UnitsAt
        (expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound n path current) x t ↔
      scheduleAtomUnitsValid role childBound pivotBound ranges n (expandedAtomValues role n current x) t := by
  induction n generalizing path x with
  | zero =>
    simp only [expandedScheduleRanges, expandedScheduledTemplate, WordRangeDecoration.UnitsAt,
      scheduleAtomUnitsValid, List.forall_mem_map]
    exact forall₂_congr fun r _ => r.toWord_coprime current x t.natAbs
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
    simp only [expandedScheduleRanges, expandedScheduledTemplate, WordRangeDecoration.UnitsAt,
      hp, scheduleAtomUnitsValid, List.forall_mem_map]
    apply and_congr (forall₂_congr fun r _ => r.toWord_coprime current x t.1.natAbs)
    apply and_congr
    · convert hL using 2
      congr 2
      exact Subsingleton.elim _ _
    · convert hR using 2
      congr 2
      exact Subsingleton.elim _ _

end Ostmann

end OAI
