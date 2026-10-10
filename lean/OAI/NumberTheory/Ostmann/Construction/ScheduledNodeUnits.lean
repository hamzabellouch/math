import OAI.NumberTheory.Ostmann.Construction.ScheduledNodeFrequencies
import OAI.NumberTheory.Ostmann.Construction.FullAtomTransferWeight

namespace OAI

/-! # Original full-weight unit guards at every reconstructed preorder node -/

namespace Ostmann
open scoped Classical

def ScheduleNodeUnits {I : Type*} (role : I → CopyScheduleRole)
    (node : ReconstructedTransferNode (ScheduleAtomState role)) : Prop :=
  ∀ v : CopyScheduleAtoms role node.state.1, (node.state.2 v).Coprime node.root.natAbs

theorem scheduleAtomUnitsValid_nodeList {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n C t) :
    ∀ node ∈ transferNodeList (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩ t,
      ScheduleNodeUnits role node := by
  induction n with
  | zero => simp [transferNodeList]
  | succ n ih =>
    intro node hn
    simp only [transferNodeList, List.mem_cons, List.mem_append] at hn
    rcases hn with rfl | hn | hn
    · exact (totalAtomUnitRanges_iff role (n + 1) C t.1).mp hu.1
    · exact ih _ _ hu.2.1 _ hn
    · exact ih _ _ hu.2.2 _ hn

theorem scheduledNodeValues_units {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (S : Finset ℤ) (n : ℕ) (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree S n)
    (hu : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n C
      (frequencyTreeMap Subtype.val n t)) (j : Fin (2 ^ n - 1)) :
    let p := transferPivotArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
      (frequencyTreeMap Subtype.val n t)
    ∀ v, (scheduledNodeValues role n j C p v).Coprime
      (singleTreeNodeFrequencies S n t j.val).root.natAbs := by
  have hn : transferNodeArray (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
      (frequencyTreeMap Subtype.val n t) j ∈
      transferNodeList (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩
        (frequencyTreeMap Subtype.val n t) := by
    unfold transferNodeArray
    rw [List.getD_eq_getElem _ _ (by rw [transferNodeList_length]; exact j.isLt)]
    exact List.getElem_mem _
  have h := scheduleAtomUnitsValid_nodeList role childBound pivotBound n C
    (frequencyTreeMap Subtype.val n t) hu _ hn
  have hs := scheduledNodeValues_actual role childBound pivotBound n C
    (frequencyTreeMap Subtype.val n t) j
  have hf := congrArg NodeFrequencies.root
    (transferNodeArray_frequencies (scheduleAtomSystem role childBound pivotBound) S n ⟨n, C⟩ t j)
  unfold ScheduleNodeUnits at h
  rw [hs] at h
  exact hf ▸ h

/-- Nonzero full weights already contain all validity and frequency-unit
conditions used by the sampled-history estimate. -/
theorem fullAtomTransferWeight_valid_units {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (C : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n C t ≠ 0) :
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, C⟩ t ∧
      scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n C t := by
  unfold fullAtomTransferWeight at hw
  split_ifs at hw with hg
  · exact ⟨recursiveTransferWeight_nonzero_valid _ _ _ _ _ _ hw, hg.2.1⟩
  · exact False.elim (hw rfl)

end Ostmann

end OAI
