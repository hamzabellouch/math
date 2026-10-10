import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionShapeBasic

namespace OAI

noncomputable section
namespace Ostmann.Conclusion
open Construction

def currentPositionBlockEquiv (m k l : ℕ) :
    Fin (Template.current (Template.initial m k) l).length ≃
      Fin (2^l) × Fin (bulkLeafTemplate m k l).length :=
  (finCongr (current_bulk_block_length m k l)).trans finProdFinEquiv.symm

@[simp] theorem currentPositionBlockEquiv_symm_val (m k l : ℕ)
    (b : Fin (2^l)) (i : Fin (bulkLeafTemplate m k l).length) :
    ((currentPositionBlockEquiv m k l).symm (b,i)).val=
      b.val*(bulkLeafTemplate m k l).length+i.val := by
  simp [currentPositionBlockEquiv,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem currentPositionBlockEquiv_get (m k l : ℕ)
    (b : Fin (2^l)) (i : Fin (bulkLeafTemplate m k l).length) :
    (Template.current (Template.initial m k) l)[((currentPositionBlockEquiv m k l).symm (b,i)).val]=
      (bulkLeafTemplate m k l)[i.val] := by
  have he : Template.current (Template.initial m k) l=
      List.ofFn (Fin.repeat (2^l) (fun j : Fin (bulkLeafTemplate m k l).length =>
        (bulkLeafTemplate m k l)[j.val])) := by
    rw [List.ofFn_fin_repeat,List.ofFn_getElem]
    exact current_eq_bulkLeafBlocks m k l
  simp only [he,List.getElem_ofFn,Fin.repeat,Fin.modNat]
  simp [currentPositionBlockEquiv_symm_val,Nat.add_mod,Nat.mod_eq_of_lt i.isLt]

theorem bulkLeafTemplate_length_ge (m k l : ℕ) : m ≤ (bulkLeafTemplate m k l).length := by
  simp [bulkLeafTemplate]

def currentBulkPositionEquiv (m k l : ℕ) :
    BulkPosition (Template.current (Template.initial m k) l) ≃ Fin (2^l) × Fin m where
  toFun x := ((currentPositionBlockEquiv m k l x.val).1,
    ⟨(currentPositionBlockEquiv m k l x.val).2.val,by
      apply (bulkLeafTemplate_bulk_iff m k l _).mp
      have hh := currentPositionBlockEquiv_get m k l
        (currentPositionBlockEquiv m k l x.val).1 (currentPositionBlockEquiv m k l x.val).2
      simp only [Prod.mk.eta,Equiv.symm_apply_apply] at hh
      have hp := x.property
      simp only [Fin.getElem_fin] at hp
      simpa only [hh] using hp⟩)
  invFun x := ⟨(currentPositionBlockEquiv m k l).symm
      (x.1,⟨x.2.val,x.2.isLt.trans_le (bulkLeafTemplate_length_ge m k l)⟩),by
    simp only [Fin.getElem_fin]
    rw [currentPositionBlockEquiv_get]
    exact (bulkLeafTemplate_bulk_iff m k l _).mpr x.2.isLt⟩
  left_inv x := by
    apply Subtype.ext
    apply (currentPositionBlockEquiv m k l).injective
    simp only [Equiv.apply_symm_apply]
  right_inv x := by
    apply Prod.ext
    · simp
    · apply Fin.ext
      simp

@[simp] theorem currentBulkPositionEquiv_symm_val (m k l : ℕ)
    (b : Fin (2^l)) (i : Fin m) :
    ((currentBulkPositionEquiv m k l).symm (b,i)).val.val=
      b.val*(bulkLeafTemplate m k l).length+i.val := by
  change ((currentPositionBlockEquiv m k l).symm (b,
    ⟨i.val,i.isLt.trans_le (bulkLeafTemplate_length_ge m k l)⟩)).val=_
  exact currentPositionBlockEquiv_symm_val m k l b _

@[simp] theorem currentBulkPositionEquiv_origin (m k l : ℕ)
    (b : Fin (2^l)) (i : Fin m) :
    (Template.current (Template.initial m k) l)[((currentBulkPositionEquiv m k l).symm (b,i)).val.val].origin=i.val := by
  change (Template.current (Template.initial m k) l)[((currentPositionBlockEquiv m k l).symm (b,
      ⟨i.val,i.isLt.trans_le (bulkLeafTemplate_length_ge m k l)⟩)).val].origin=i.val
  rw [currentPositionBlockEquiv_get]
  exact bulkLeafTemplate_bulk_origin m k l _ i.isLt

theorem currentBulkPosition_card (m k l : ℕ) :
    Fintype.card (BulkPosition (Template.current (Template.initial m k) l))=2^l*m := by
  rw [Fintype.card_congr (currentBulkPositionEquiv m k l)]
  simp

end Ostmann.Conclusion

end

end OAI
