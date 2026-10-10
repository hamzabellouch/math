import OAI.NumberTheory.Ostmann.Construction.ExpandedOutsideWords
import OAI.NumberTheory.Ostmann.Construction.ExpandedRangeReplay
import OAI.NumberTheory.Ostmann.Construction.WordPrimeReplay

namespace OAI

/-! # The actual Y-atom coprimalities are a finite list of original-prime checks -/

namespace Ostmann

open scoped Classical

noncomputable def expandedYPrimeCoordinates {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth)) : List V :=
  (Finset.univ.toList : List (CopyScheduleY role n)).flatMap
    (expandedYPrimeWord role depth n current)

theorem expandedYPrimeCoordinates_coprime {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current)
    (x : ExpandedScheduledVariable V depth → ℕ) (prime : V → ℕ)
    (hx : ∀ v, x (.inl v) = prime v) (P : ℕ) :
    (∀ v ∈ expandedYPrimeCoordinates role depth n current, (prime v).Coprime P) ↔
      ∀ i : CopyScheduleY role n,
        (expandedAtomValues role (n + 1) current x ⟨.inr i.val, i.property⟩).Coprime P := by
  have he (i : CopyScheduleY role n) :
      ((expandedYPrimeWord role depth n current i).map prime).prod =
        expandedAtomValues role (n + 1) current x ⟨.inr i.val, i.property⟩ := by
    rw [← expandedYPrimeWord_product role depth n current hc i x]
    congr 1
    exact List.map_congr_left (fun v _ => (hx v).symm)
  constructor
  · intro h i
    rw [← he i, Nat.coprime_list_prod_left_iff]
    intro p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    exact h v (List.mem_flatMap.mpr ⟨i, by simp, hv⟩)
  · intro h v hv
    obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
    have hi := h i
    rw [← he i, Nat.coprime_list_prod_left_iff] at hi
    exact hi _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

noncomputable def expandedSchedulePrimes {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth : ℕ) :
    (n : ℕ) → List Bool →
      (CopyScheduleAtoms role n → List (ExpandedScheduledVariable V depth)) → WordPrimeDecoration V n
  | 0, _, _ => .leaf
  | n + 1, path, current => .node (expandedYPrimeCoordinates role depth n current)
      (expandedSchedulePrimes role depth n (true :: path)
        (reverseCopyLabelMap role n true [expandedPivotAddress V depth n path] current))
      (expandedSchedulePrimes role depth n (false :: path)
        (reverseCopyLabelMap role n false [expandedPivotAddress V depth n path] current))

noncomputable def scheduleAtomCoprimalitiesValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, _, _ => True
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ i : CopyScheduleY role n, (x ⟨.inr i.val, i.property⟩).Coprime P) ∧
        scheduleAtomCoprimalitiesValid role childBound pivotBound n
          (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomCoprimalitiesValid role childBound pivotBound n
          (reverseCopyLabelMap role n false P x) t.2.2

theorem expandedSchedulePrimes_valid_iff {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable V depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (ha : ExpandedActualCoordinates role depth n current)
    (x : ExpandedScheduledVariable V depth → ℕ) (prime : V → ℕ)
    (hx : ∀ v, x (.inl v) = prime v) (t : FrequencyTree ℤ n) :
    (expandedSchedulePrimes role depth n path current).ValidAt
        (expandedScheduledTemplate role (expandedPivotAddress V depth) childBound pivotBound n path current)
        x prime t ↔
      scheduleAtomCoprimalitiesValid role childBound pivotBound n
        (expandedAtomValues role n current x) t := by
  induction n generalizing path x with
  | zero => rfl
  | succ n ih =>
    let P := historyPivot (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, expandedAtomValues role (n + 1) current x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    have hn' : n ≤ depth := by omega
    have hx' (v : V) :
        Function.update x (expandedPivotAddress V depth n path) P (.inl v) = prime v := by
      simpa only [expandedPivotAddress, Function.update_of_ne (Sum.inl_ne_inr)] using hx v
    have hL := ih hn' (true :: path)
      (reverseCopyLabelMap role n true [expandedPivotAddress V depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' true path current hc)
      (reverseExpandedActualCoordinates role depth n true _ current ha)
      (Function.update x (expandedPivotAddress V depth n path) P) hx' t.2.1
    have hR := ih hn' (false :: path)
      (reverseCopyLabelMap role n false [expandedPivotAddress V depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' false path current hc)
      (reverseExpandedActualCoordinates role depth n false _ current ha)
      (Function.update x (expandedPivotAddress V depth n path) P) hx' t.2.2
    rw [expanded_schedule_child_state role depth n hn' true path current hc x P] at hL
    rw [expanded_schedule_child_state role depth n hn' false path current hc x P] at hR
    have hp := expanded_schedule_pivot_eq role (expandedPivotAddress V depth)
      childBound pivotBound n path current x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    dsimp only [expandedScheduledTemplate] at hp
    simp only [expandedSchedulePrimes, expandedScheduledTemplate, WordPrimeDecoration.ValidAt,
      hp, scheduleAtomCoprimalitiesValid]
    apply and_congr (expandedYPrimeCoordinates_coprime role depth n current ha x prime hx P)
    apply and_congr
    · convert hL using 2
      congr 2
      exact Subsingleton.elim _ _
    · convert hR using 2
      congr 2
      exact Subsingleton.elim _ _

end Ostmann

end OAI
