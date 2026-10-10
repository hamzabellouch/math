import OAI.NumberTheory.Ostmann.Construction.ScheduledBulkMatchingCount
import OAI.NumberTheory.Ostmann.Construction.ScheduledWordLeafProducts
import OAI.NumberTheory.Ostmann.Tree.ArrangementReindex

namespace OAI

/-! # The counted bulk slots are the actual recursive arithmetic leaves -/

namespace Ostmann
open scoped Classical

noncomputable def treeLeafPathEquiv (n : ℕ) : TreeLeafIndex n ≃ (Fin n → Bool) :=
  Equiv.ofBijective (treeLeafCopyPath n) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨treeLeafCopyPath_injective n, by simp [card_treeLeafIndex]⟩)

noncomputable def treeLeafEnumeration (n : ℕ) : TreeLeafIndex n ≃ Fin (2 ^ n) :=
  (treeLeafPathEquiv n).trans (scheduledPathEnumeration n).symm

@[simp] theorem scheduledPathEnumeration_treeLeafEnumeration (n : ℕ) (t : TreeLeafIndex n) :
    scheduledPathEnumeration n (treeLeafEnumeration n t) = treeLeafCopyPath n t := by
  simp only [treeLeafEnumeration, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

noncomputable def scheduledTreeBulkCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) :
    (TreeLeafIndex n × Fin m) ≃
      {h : CopyScheduleH role n // copyScheduleRole role n h.val = .word} :=
  ((treeLeafEnumeration n).prodCongr (Equiv.refl _)).trans
    (scheduledBulkCoordinates role n m word)

@[simp] theorem scheduledTreeBulkCoordinates_leaf {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) (t : TreeLeafIndex n) (i : Fin m) :
    (scheduledTreeBulkCoordinates role n m word (t, i)).val =
      wordLeafHSlot role (word i).val (word i).property n t := by
  apply Subtype.ext
  change copySchedulePath n (scheduledPathEnumeration n (treeLeafEnumeration n t)) (word i).val = _
  rw [scheduledPathEnumeration_treeLeafEnumeration]
  rfl

noncomputable def scheduledTreeBulkMatching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n)) :
    Equiv.Perm (TreeLeafIndex n × Fin m) :=
  reindexArrangement (treeLeafEnumeration n).symm
    (separatedMatchingLeft (scheduledSeparatedMatching role n m word e))

theorem separatedMatchingLeft_apply {A B : Type*}
    (e : PartitionMatching (@sumSide A B) (@sumSide A B)) (a : A) :
    e.val (.inl a) = .inl (separatedMatchingLeft e a) := by
  have h := congrArg Subtype.val ((sumSideLeftEquiv A B).apply_symm_apply
    ((e.restrict true) (sumSideLeftEquiv A B a)))
  change Sum.inl (separatedMatchingLeft e a) = e.val (.inl a) at h
  exact h.symm

@[simp] theorem scheduledSplitHCoordinates_inl {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) (x : Fin (2 ^ n) × Fin m) :
    scheduledSplitHCoordinates role n m word (.inl x) =
      (scheduledBulkCoordinates role n m word x).val := rfl

theorem scheduledBulkMatching_slot {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n))
    (x : Fin (2 ^ n) × Fin m) :
    e.val (scheduledBulkCoordinates role n m word x).val =
      (scheduledBulkCoordinates role n m word
        (separatedMatchingLeft (scheduledSeparatedMatching role n m word e) x)).val := by
  have h := congrArg (scheduledSplitHCoordinates role n m word)
    (separatedMatchingLeft_apply (scheduledSeparatedMatching role n m word e) x)
  simpa only [scheduledSeparatedMatching, Equiv.trans_apply, Equiv.apply_symm_apply,
    scheduledSplitHCoordinates_inl] using h

theorem scheduledTreeBulkMatching_slot {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n))
    (x : TreeLeafIndex n × Fin m) :
    e.val (scheduledTreeBulkCoordinates role n m word x).val =
      (scheduledTreeBulkCoordinates role n m word
        (scheduledTreeBulkMatching role n m word e x)).val := by
  have h := scheduledBulkMatching_slot role n m word e
    ((treeLeafEnumeration n).prodCongr (Equiv.refl _) x)
  simpa only [scheduledTreeBulkMatching, scheduledTreeBulkCoordinates,
    reindexArrangement, Equiv.trans_apply, Equiv.symm_symm, Equiv.prodCongr_apply,
    Equiv.refl_apply, Prod.map, Equiv.apply_symm_apply, Prod.mk.eta] using h

theorem scheduledTreeBulkMatching_symm_slot {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n))
    (x : TreeLeafIndex n × Fin m) :
    e.val.symm (scheduledTreeBulkCoordinates role n m word x).val =
      (scheduledTreeBulkCoordinates role n m word
        ((scheduledTreeBulkMatching role n m word e).symm x)).val := by
  apply e.val.injective
  rw [e.val.apply_symm_apply, scheduledTreeBulkMatching_slot, Equiv.apply_symm_apply]

theorem scheduledTreeBulkMatching_good {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n))
    (he : ¬ BadScheduledMatching role n m word e) :
    4 * Fintype.card (arrangementGraph m (scheduledTreeBulkMatching role n m word e)).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex n) := by
  rw [scheduledTreeBulkMatching, arrangement_component_count_reindex, card_treeLeafIndex]
  exact Nat.le_of_not_gt he

end Ostmann

end OAI
