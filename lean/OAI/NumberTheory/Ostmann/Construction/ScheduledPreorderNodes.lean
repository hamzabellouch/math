import OAI.NumberTheory.Ostmann.Construction.ScheduleAtomSystem
import OAI.NumberTheory.Ostmann.Construction.PreorderTransferPaths
import OAI.NumberTheory.Ostmann.Construction.ScheduledNodeSources

namespace OAI

/-! # Preorder pivots reproduce the literal scheduled atom assignments -/

namespace Ostmann
open scoped Classical

noncomputable def transferNodeArray {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (j : Fin (2 ^ n - 1)) :
    ReconstructedTransferNode State :=
  (transferNodeList sys n σ t).getD j.val ⟨σ, 0, 0, 0⟩

noncomputable def transferPivotArray {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) : Fin (2 ^ n - 1) → ℕ :=
  fun j => (transferNodeArray sys n σ t j).pivot sys

theorem transferNodeArray_path {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (j : Fin (2 ^ n - 1)) :
    transferNodeArray sys n σ t j = transferNodeAtPath sys n σ t (preorderNodePath n j) := by
  unfold transferNodeArray
  rw [← nodePathIndex_preorderNodePath n j]
  exact transferNodeList_get_path sys n σ t _ (preorderNodePath_length n j) _

theorem transferNodeArray_valid {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (hv : ValidTransferHistory sys n σ t)
    (j : Fin (2 ^ n - 1)) : (transferNodeArray sys n σ t j).Valid sys := by
  rw [transferNodeArray_path]
  exact transferNodeAtPath_valid sys n σ t hv _ (preorderNodePath_length n j)

theorem replayNodeIndices_preorder {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (j : Fin (2 ^ n - 1)) :
    replayNodeIndices sys (preorderNodePath n j) 0
      (nodeAncestorValues n j (transferPivotArray sys n σ t)) σ =
        (transferNodeArray sys n σ t j).state := by
  rw [transferNodeArray_path]
  apply replayNodeIndices_actual sys n σ t _ (preorderNodePath_length n j)
  intro k hk
  simp only [Nat.zero_add, nodeAncestorValues, dite_eq_left hk, transferPivotArray]
  rw [transferNodeArray_path, ancestorNodeIndex_path]

def reversePathOfList (path : List Bool) : Fin path.length → Bool :=
  fun j => !(path[j.val])

theorem replayNodeIndices_schedule {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (path : List Bool) (n d : ℕ) (p : ℕ → ℕ)
    (C : CopyScheduleAtoms role (n + path.length) → ℕ) :
    replayNodeIndices (scheduleAtomSystem role childBound pivotBound) path d p
        ⟨n + path.length, C⟩ =
      ⟨n, descendAtomValues role path.length n d (reversePathOfList path) p C⟩ := by
  induction path generalizing d with
  | nil => rfl
  | cons b path ih =>
    have htail : Fin.tail (reversePathOfList (b :: path)) = reversePathOfList path := by
      funext j
      rfl
    cases b
    · change replayNodeIndices (scheduleAtomSystem role childBound pivotBound) path (d + 1) p
        ⟨n + path.length, reverseCopyLabelMap role (n + path.length) true (p d) C⟩ = _
      rw [ih]
      simp only [List.length_cons, descendAtomValues, htail]
      rfl
    · change replayNodeIndices (scheduleAtomSystem role childBound pivotBound) path (d + 1) p
        ⟨n + path.length, reverseCopyLabelMap role (n + path.length) false (p d) C⟩ = _
      rw [ih]
      simp only [List.length_cons, descendAtomValues, htail]
      rfl

/-- The source-environment assignment is precisely the state of the actual
preorder history node, with its actual reconstructed natural pivots. -/
theorem scheduledNodeValues_actual {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (j : Fin (2 ^ n - 1)) :
    (transferNodeArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩ t j).state =
      ⟨scheduledNodeLevel n j + 1, scheduledNodeValues role n j C
        (transferPivotArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩ t)⟩ := by
  rw [← replayNodeIndices_preorder]
  have hcast : (⟨scheduledNodeLevel n j + 1 + (preorderNodePath n j).length,
      fun v => C (scheduledNodeRootEquiv role n j v)⟩ : ScheduleAtomState role) = ⟨n, C⟩ := by
    have cast_state : ∀ {a b : ℕ} (e : a = b) (f : CopyScheduleAtoms role b → ℕ),
        (⟨a, fun v => f (Equiv.cast (congrArg (CopyScheduleAtoms role) e) v)⟩ :
          ScheduleAtomState role) = ⟨b, f⟩ := by
      intro a b e f
      subst b
      rfl
    exact cast_state (scheduledNodeLevel_add_depth n j) C
  rw [← hcast]
  exact replayNodeIndices_schedule role childBound pivotBound _ _ 0 _ _

end Ostmann

end OAI
