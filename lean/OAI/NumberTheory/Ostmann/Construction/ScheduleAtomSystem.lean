import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduleCoordinates

namespace OAI

/-! # The literal reverse transfer system on current atom values -/

namespace Ostmann

open scoped BigOperators Classical

abbrev ScheduleAtomState {I : Type*} (role : I → CopyScheduleRole) :=
  Σ n : ℕ, CopyScheduleAtoms role n → ℕ

noncomputable def scheduleAtomLeft {I : Type*} [Fintype I] (role : I → CopyScheduleRole) :
    ScheduleAtomState role → ℕ
  | ⟨0, _⟩ => 1
  | ⟨n + 1, x⟩ => ∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩

noncomputable def scheduleAtomRight {I : Type*} [Fintype I] (role : I → CopyScheduleRole) :
    ScheduleAtomState role → ℕ
  | ⟨0, _⟩ => 1
  | ⟨n + 1, x⟩ => ∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩

def scheduleAtomBound {I : Type*} (role : I → CopyScheduleRole) (bound : ℕ → ℕ) :
    ScheduleAtomState role → ℕ
  | ⟨0, _⟩ => 0
  | ⟨n + 1, _⟩ => bound n

noncomputable def scheduleAtomChild {I : Type*} (role : I → CopyScheduleRole) (b : Bool) :
    ScheduleAtomState role → ℕ → ScheduleAtomState role
  | ⟨0, x⟩, _ => ⟨0, x⟩
  | ⟨n + 1, x⟩, P => ⟨n, reverseCopyLabelMap role n b P x⟩

noncomputable def scheduleAtomSystem {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (childBound pivotBound : ℕ → ℕ) : TransferHistorySystem (ScheduleAtomState role) where
  leftProduct := scheduleAtomLeft role
  rightProduct := scheduleAtomRight role
  childBound := scheduleAtomBound role childBound
  pivotBound := scheduleAtomBound role pivotBound
  leftState := scheduleAtomChild role true
  rightState := scheduleAtomChild role false

noncomputable def expandedAtomValues {I σ : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (current : CopyScheduleAtoms role n → List σ) (x : σ → ℕ) : CopyScheduleAtoms role n → ℕ :=
  fun i => ((current i).map x).prod

theorem expanded_schedule_node_iff {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (path : List Bool) (current : CopyScheduleAtoms role (n + 1) → List σ)
    (x : σ → ℕ) (s v w : ℤ) (P : ℕ) :
    ValidTransferNode (wordTransferSystem σ)
      ((expandedScheduledTemplate role address childBound pivotBound (n + 1) path current).state x) s v w P ↔
    ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, expandedAtomValues role (n + 1) current x⟩ s v w P := by
  let wordState := (expandedScheduledTemplate role address childBound pivotBound (n + 1) path current).state x
  let atomState : ScheduleAtomState role := ⟨n + 1, expandedAtomValues role (n + 1) current x⟩
  have hL : (wordTransferSystem σ).leftProduct wordState =
      (scheduleAtomSystem role childBound pivotBound).leftProduct atomState :=
    expandedHWord_product role n true current x
  have hR : (wordTransferSystem σ).rightProduct wordState =
      (scheduleAtomSystem role childBound pivotBound).rightProduct atomState :=
    expandedHWord_product role n false current x
  have hPB : (wordTransferSystem σ).pivotBound wordState =
      (scheduleAtomSystem role childBound pivotBound).pivotBound atomState := rfl
  have hCB : (wordTransferSystem σ).childBound wordState =
      (scheduleAtomSystem role childBound pivotBound).childBound atomState := rfl
  dsimp only [wordState, atomState] at hL hR hPB hCB
  constructor
  · intro h
    exact ⟨h.root_ne_zero, by simpa only [hR] using h.root_unit,
      by simpa only [hL, hR] using h.relation, h.pivot_pos, h.pivot_bound,
      h.left_bound, h.right_bound, by simpa only [hR, hPB, hCB] using h.range_gap, h.pivot_unit⟩
  · intro h
    exact ⟨h.root_ne_zero, by simpa only [hR] using h.root_unit,
      by simpa only [hL, hR] using h.relation, h.pivot_pos, h.pivot_bound,
      h.left_bound, h.right_bound, by simpa only [hR, hPB, hCB] using h.range_gap, h.pivot_unit⟩

/-- The inserted coordinate realizes exactly the original child atom state,
with composite atoms evaluated as their constituent prime products. -/
theorem expanded_schedule_child_state {I α : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ) (hn : n ≤ depth) (b : Bool) (path : List Bool)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter (n + 1) v)
    (x : ExpandedScheduledVariable α depth → ℕ) (P : ℕ) :
    expandedAtomValues role n
      (reverseCopyLabelMap role n b [expandedPivotAddress α depth n path] current)
      (Function.update x (expandedPivotAddress α depth n path) P) =
      reverseCopyLabelMap role n b P (expandedAtomValues role (n + 1) current x) := by
  funext i
  unfold expandedAtomValues
  exact reverseCopyLabelMap_product_update role n b _ P current x
    (fun j v hv => expandedPivotAddress_fresh hn path v (hc j v hv)) i

end Ostmann

end OAI
