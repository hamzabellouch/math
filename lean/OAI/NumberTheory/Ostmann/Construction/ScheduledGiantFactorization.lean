import OAI.NumberTheory.Ostmann.Construction.ScheduledAllBulkProducts
import OAI.NumberTheory.Ostmann.Arithmetic.NodeBulkProducts

namespace OAI

/-! # Separating a designated giant from the actual child products -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def scheduledRegularCoefficient {I G : Type*} [Fintype I] [CommMonoid G]
    (role : I → CopyScheduleRole) (n : ℕ) (giant : ScheduledNonbulkH role n)
    (x : CopyScheduleH role n → G) : G :=
  ∏ h ∈ (Finset.univ : Finset (ScheduledNonbulkH role n)).erase giant, x h.val

theorem scheduled_H_giant_regular_bulk {I G : Type*} [Fintype I] [CommMonoid G]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (giant : ScheduledNonbulkH role n)
    (x : CopyScheduleH role n → G) :
    (∏ h, x h) = x giant.val * scheduledRegularCoefficient role n giant x *
      treeLeafProduct n ((treeLeafTupleEquiv G n).symm
        (fun t => ∏ i : Fin m, x (scheduledTreeBulkCoordinates role n m word (t, i)).val)) := by
  rw [scheduledTree_H_product role n m word, treeLeafProduct_indexed]
  congr 1
  exact (Finset.mul_prod_erase (Finset.univ : Finset (ScheduledNonbulkH role n))
    (fun h => x h.val) (Finset.mem_univ giant)).symm

theorem scheduled_child_giant_regular_bulk {I G : Type*} [Fintype I] [CommMonoid G]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (giant : ScheduledNonbulkH role n)
    (b : Bool) (x : CopyScheduleAtoms role (n + 1) → G) :
    (∏ h : CopyScheduleH role n, x ⟨.inl (b, h.val), h.property⟩) =
      x ⟨.inl (b, giant.val.val), giant.val.property⟩ *
        scheduledRegularCoefficient role n giant
          (fun h => x ⟨.inl (b, h.val), h.property⟩) *
        treeLeafProduct n ((treeLeafTupleEquiv G n).symm
          (fun t => ∏ i : Fin m, x (wordLeafSlot role (word i).val (word i).property (n + 1)
            (if b then .inl t else .inr t)))) := by
  rw [scheduled_H_giant_regular_bulk role n m word giant]
  congr 2
  apply congrArg (treeLeafTupleEquiv G n).symm
  funext t
  apply Finset.prod_congr rfl
  intro i _
  rw [scheduledTreeBulkCoordinates_leaf]
  congr 1
  exact copied_wordLeafHSlot role (word i).val (word i).property n b t

end Ostmann

end OAI
