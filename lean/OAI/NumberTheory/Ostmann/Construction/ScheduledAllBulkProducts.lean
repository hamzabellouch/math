import OAI.NumberTheory.Ostmann.Construction.ScheduledTreeBulkCoordinates

namespace OAI

/-! # Full bulk products in each actual arithmetic child -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def scheduledTreeSplitHCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) :
    ((TreeLeafIndex n × Fin m) ⊕ ScheduledNonbulkH role n) ≃ CopyScheduleH role n :=
  (Equiv.sumCongr ((treeLeafEnumeration n).prodCongr (Equiv.refl _)) (Equiv.refl _)).trans
    (scheduledSplitHCoordinates role n m word)

@[simp] theorem scheduledTreeSplitHCoordinates_inl {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) (x : TreeLeafIndex n × Fin m) :
    scheduledTreeSplitHCoordinates role n m word (.inl x) =
      (scheduledTreeBulkCoordinates role n m word x).val := rfl

@[simp] theorem scheduledTreeSplitHCoordinates_inr {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) (h : ScheduledNonbulkH role n) :
    scheduledTreeSplitHCoordinates role n m word (.inr h) = h.val := rfl

theorem scheduledTree_H_product {I G : Type*} [Fintype I] [CommMonoid G]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (x : CopyScheduleH role n → G) :
    (∏ h, x h) = (∏ h : ScheduledNonbulkH role n, x h.val) *
      ∏ t : TreeLeafIndex n, ∏ i : Fin m, x (scheduledTreeBulkCoordinates role n m word (t, i)).val := by
  rw [← (scheduledTreeSplitHCoordinates role n m word).prod_comp]
  rw [Fintype.prod_sum_type]
  simp only [scheduledTreeSplitHCoordinates_inl, scheduledTreeSplitHCoordinates_inr]
  rw [Fintype.prod_prod_type]
  exact mul_comm _ _

theorem scheduled_child_H_product {I G : Type*} [Fintype I] [CommMonoid G]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (b : Bool)
    (x : CopyScheduleAtoms role (n + 1) → G) :
    (∏ h : CopyScheduleH role n, x ⟨.inl (b, h.val), h.property⟩) =
      (∏ h : ScheduledNonbulkH role n, x ⟨.inl (b, h.val.val), h.val.property⟩) *
        ∏ t : TreeLeafIndex n, ∏ i : Fin m,
          x (wordLeafSlot role (word i).val (word i).property (n + 1)
            (if b then .inl t else .inr t)) := by
  rw [scheduledTree_H_product role n m word]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro i _
  rw [scheduledTreeBulkCoordinates_leaf]
  congr 1
  exact copied_wordLeafHSlot role (word i).val (word i).property n b t

end Ostmann

end OAI
