import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionShapeOrder
import OAI.NumberTheory.Ostmann.Construction.DiagonalPermutationCountBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction.DiagonalPermutationCount
open Conclusion

abbrev remainingTemplate (m k l : ℕ) :=
  Template.remainder (l+1) (Template.current (Template.initial m k) l)

def bulkPositionSlotEquiv (T : List SourceSlot) :
    BulkPosition T ≃ Conclusion.BulkPosition T where
  toFun x := by
    obtain ⟨i,hi⟩ := x
    induction i using Fin.cases with
    | zero => simp [remainingPositionBand] at hi
    | succ i => exact ⟨i,by simpa [remainingPositionBand] using hi⟩
  invFun x := ⟨x.val.succ,by simpa [remainingPositionBand] using x.property⟩
  left_inv x := by
    obtain ⟨i,hi⟩ := x
    induction i using Fin.cases with
    | zero => simp [remainingPositionBand] at hi
    | succ i => rfl
  right_inv x := rfl

@[simp] theorem bulkPositionSlotEquiv_symm_val (T : List SourceSlot)
    (x : Conclusion.BulkPosition T) :
    ((bulkPositionSlotEquiv T).symm x).val=x.val.succ := rfl

def remainderPositionBlockEquiv (m k l : ℕ) :
    Fin (remainingTemplate m k l).length ≃
      Fin (2^l) × Fin (bulkLeafTemplate m k (l+1)).length :=
  (finCongr (current_remainder_bulk_block_length m k l)).trans finProdFinEquiv.symm

@[simp] theorem remainderPositionBlockEquiv_symm_val (m k l : ℕ)
    (b : Fin (2^l)) (i : Fin (bulkLeafTemplate m k (l+1)).length) :
    ((remainderPositionBlockEquiv m k l).symm (b,i)).val=
      b.val*(bulkLeafTemplate m k (l+1)).length+i.val := by
  simp [remainderPositionBlockEquiv,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem remainderPositionBlockEquiv_get (m k l : ℕ)
    (b : Fin (2^l)) (i : Fin (bulkLeafTemplate m k (l+1)).length) :
    (remainingTemplate m k l)[((remainderPositionBlockEquiv m k l).symm (b,i)).val]=
      (bulkLeafTemplate m k (l+1))[i.val] := by
  have he : remainingTemplate m k l=
      List.ofFn (Fin.repeat (2^l) (fun j : Fin (bulkLeafTemplate m k (l+1)).length =>
        (bulkLeafTemplate m k (l+1))[j.val])) := by
    rw [List.ofFn_fin_repeat,List.ofFn_getElem]
    exact current_remainder_eq_bulkLeafBlocks m k l
  simp only [he,List.getElem_ofFn,Fin.repeat,Fin.modNat]
  simp only [remainderPositionBlockEquiv_symm_val,Nat.add_mod,Nat.mul_mod,
    Nat.mod_self,Nat.mul_zero,Nat.zero_mod,Nat.zero_add,Nat.mod_eq_of_lt i.isLt]

def remainderSlotBulkEquiv (m k l : ℕ) :
    Conclusion.BulkPosition (remainingTemplate m k l) ≃ Fin (2^l) × Fin m where
  toFun x := ((remainderPositionBlockEquiv m k l x.val).1,
    ⟨(remainderPositionBlockEquiv m k l x.val).2.val,by
      apply (bulkLeafTemplate_bulk_iff m k (l+1) _).mp
      have hh := remainderPositionBlockEquiv_get m k l
        (remainderPositionBlockEquiv m k l x.val).1 (remainderPositionBlockEquiv m k l x.val).2
      simp only [Prod.mk.eta,Equiv.symm_apply_apply] at hh
      have hp := x.property
      simp only [Fin.getElem_fin] at hp
      simpa only [hh] using hp⟩)
  invFun x := ⟨(remainderPositionBlockEquiv m k l).symm
      (x.1,⟨x.2.val,x.2.isLt.trans_le (bulkLeafTemplate_length_ge m k (l+1))⟩),by
    simp only [Fin.getElem_fin]
    rw [remainderPositionBlockEquiv_get]
    exact (bulkLeafTemplate_bulk_iff m k (l+1) _).mpr x.2.isLt⟩
  left_inv x := by
    apply Subtype.ext
    apply (remainderPositionBlockEquiv m k l).injective
    simp only [Equiv.apply_symm_apply]
  right_inv x := by
    apply Prod.ext
    · simp
    · apply Fin.ext
      simp

def remainderBulkPositionEquiv (m k l : ℕ) :
    BulkPosition (remainingTemplate m k l) ≃ Fin (2^l) × Fin m :=
  (bulkPositionSlotEquiv _).trans (remainderSlotBulkEquiv m k l)

@[simp] theorem remainderBulkPositionEquiv_symm_val (m k l : ℕ)
    (b : Fin (2^l)) (i : Fin m) :
    ((remainderBulkPositionEquiv m k l).symm (b,i)).val.val=
      b.val*(bulkLeafTemplate m k (l+1)).length+i.val+1 := by
  change ((remainderPositionBlockEquiv m k l).symm (b,
    ⟨i.val,i.isLt.trans_le (bulkLeafTemplate_length_ge m k (l+1))⟩)).val+1=_
  rw [remainderPositionBlockEquiv_symm_val]

@[simp] theorem remainderSlotBulkEquiv_origin (m k l : ℕ)
    (b : Fin (2^l)) (i : Fin m) :
    (remainingTemplate m k l)[((remainderSlotBulkEquiv m k l).symm (b,i)).val.val].origin=i.val := by
  change (remainingTemplate m k l)[((remainderPositionBlockEquiv m k l).symm (b,
      ⟨i.val,i.isLt.trans_le (bulkLeafTemplate_length_ge m k (l+1))⟩)).val].origin=i.val
  rw [remainderPositionBlockEquiv_get]
  exact bulkLeafTemplate_bulk_origin m k (l+1) _ i.isLt

theorem remainder_bulk_card (m k l : ℕ) :
    Fintype.card (BulkPosition (remainingTemplate m k l))=2^l*m := by
  rw [Fintype.card_congr (remainderBulkPositionEquiv m k l)]
  simp

theorem remainder_nonbulk_card (m k l : ℕ) :
    Fintype.card (NonbulkPosition (remainingTemplate m k l))=
      (remainingTemplate m k l).length+1-2^l*m := by
  rw [Fintype.card_subtype_compl,remainder_bulk_card]
  simp only [RemainingIndex,Fintype.card_fin]

end Ostmann.Construction.DiagonalPermutationCount

end

end OAI
