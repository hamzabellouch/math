import OAI.NumberTheory.Ostmann.Construction.ScheduledPreorderNodes
import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveFrequencySupport

namespace OAI

/-! # The exact frequency triple of each reconstructed scheduled node -/

namespace Ostmann

def ReconstructedTransferNode.frequencies {State : Type*}
    (node : ReconstructedTransferNode State) : NodeFrequencies :=
  ⟨node.root, node.left, node.right⟩

theorem transferNodeList_frequencies {State : Type*} (sys : TransferHistorySystem State)
    (S : Finset ℤ) (n : ℕ) (σ : State) (t : FrequencyTree S n) :
    (transferNodeList sys n σ (frequencyTreeMap Subtype.val n t)).map
      ReconstructedTransferNode.frequencies = singleFrequencySplitList S n t := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [transferNodeList, frequencyTreeMap, frequencyRoot_map, List.map_cons,
      List.map_append, ih, singleFrequencySplitList, ReconstructedTransferNode.frequencies]

theorem transferNodeArray_frequencies {State : Type*} (sys : TransferHistorySystem State)
    (S : Finset ℤ) (n : ℕ) (σ : State) (t : FrequencyTree S n) (j : Fin (2 ^ n - 1)) :
    (transferNodeArray sys n σ (frequencyTreeMap Subtype.val n t) j).frequencies =
      singleTreeNodeFrequencies S n t j.val := by
  have he := congrArg (fun L => L.getD j.val emptyNodeFrequencies)
    (transferNodeList_frequencies sys S n σ t)
  have hm := List.getD_map (transferNodeList sys n σ (frequencyTreeMap Subtype.val n t))
    ⟨σ, 0, 0, 0⟩ ReconstructedTransferNode.frequencies (n := j.val)
  exact hm.symm.trans he

/-- Validity at a node now uses the frequency triple of that exact preorder
entry, with no independently supplied node relation. -/
theorem scheduledNodeValues_valid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (S : Finset ℤ) (n : ℕ) (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree S n)
    (hv : ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
      (frequencyTreeMap Subtype.val n t)) (j : Fin (2 ^ n - 1)) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
      (frequencyTreeMap Subtype.val n t)
    let f := singleTreeNodeFrequencies S n t j.val
    ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨scheduledNodeLevel n j + 1, scheduledNodeValues role n j C p⟩
      f.root f.left f.right (p j) := by
  dsimp only
  have hh := transferNodeArray_valid (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
    (frequencyTreeMap Subtype.val n t) hv j
  have hf := transferNodeArray_frequencies (scheduleAtomSystem role childBound pivotBound) S n ⟨n, C⟩ t j
  have hs := scheduledNodeValues_actual role childBound pivotBound n C
    (frequencyTreeMap Subtype.val n t) j
  rw [ReconstructedTransferNode.Valid, hs] at hh
  have hroot := congrArg NodeFrequencies.root hf
  have hleft := congrArg NodeFrequencies.left hf
  have hright := congrArg NodeFrequencies.right hf
  exact hroot ▸ hleft ▸ hright ▸ hh

end Ostmann

end OAI
