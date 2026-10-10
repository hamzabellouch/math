import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.LinearEvenMoment
import OAI.Probability.BinarySweep.Conditional.ConditionalAverage
import OAI.Probability.BinarySweep.GridBounds.GridSplitSweep

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

@[simp] lemma left_join (x : GridSlot (leftBits bits)) (y : GridSlot (rightBits bits)) :
    leftSlot bits (joinSlot bits x y)=x := by funext i; simp [leftSlot,joinSlot]
@[simp] lemma right_join (x : GridSlot (leftBits bits)) (y : GridSlot (rightBits bits)) :
    rightSlot bits (joinSlot bits x y)=y := by funext i; simp [rightSlot,joinSlot]
@[simp] lemma join_left_right (x : GridSlot bits) :
    joinSlot bits (leftSlot bits x) (rightSlot bits x)=x := (slotEquiv bits).symm_apply_apply x

def rowFreeEquiv (t : Fin (m+1)) : FreeSlot H (leftTime t) ≃
    Σy : GridSlot (rightBits bits), FreeSlot (rowFamily bits H y) t where
  toFun x := ⟨rightSlot bits x.val,⟨leftSlot bits x.val,by
    rintro ⟨a,ha⟩
    let k := (Fintype.equivFin (RowLabels bits H (rightSlot bits x.val))).symm a
    apply x.property
    refine ⟨k.val,?_⟩
    apply (slotEquiv bits).injective
    apply Prod.ext
    · exact ha
    · exact (rightSlot_leftTime bits H t k.val).trans k.property⟩⟩
  invFun yx := ⟨joinSlot bits yx.2.val yx.1,by
    rintro ⟨k,hk⟩
    have he := congrArg (slotEquiv bits) hk
    have hr : rightSlot bits (H.position 0 k)=yx.1 := by
      rw [←rightSlot_leftTime bits H t k]
      exact (congrArg Prod.snd he).trans (congrArg Prod.snd ((slotEquiv bits).apply_symm_apply (yx.2.val,yx.1)))
    apply yx.2.property
    refine ⟨Fintype.equivFin (RowLabels bits H yx.1) ⟨k,hr⟩,?_⟩
    simp only [rowFamily,Equiv.symm_apply_apply]
    exact (congrArg Prod.fst he).trans (congrArg Prod.fst ((slotEquiv bits).apply_symm_apply (yx.2.val,yx.1)))⟩
  left_inv x := by
    apply Subtype.ext
    exact (slotEquiv bits).symm_apply_apply x.val
  right_inv yx := by
    rcases yx with ⟨y,x⟩
    have he := (slotEquiv bits).apply_symm_apply (x.val,y)
    apply Sigma.ext (congrArg Prod.snd he)
    have hr : rightSlot bits (joinSlot bits x.val y)=y := congrArg Prod.snd he
    apply (Subtype.heq_iff_coe_eq (by
      intro a
      change a∉Set.range ((rowFamily bits H (rightSlot bits (joinSlot bits x.val y))).position t) ↔ _
      rw [hr])).mpr
    exact congrArg Prod.fst he

def columnFreeEquiv (t : Fin (n+1)) : FreeSlot H (rightTime t) ≃
    Σx : GridSlot (leftBits bits), FreeSlot (columnFamily bits H x) t where
  toFun y := ⟨leftSlot bits y.val,⟨rightSlot bits y.val,by
    rintro ⟨a,ha⟩
    let k := (Fintype.equivFin (ColumnLabels bits H (leftSlot bits y.val))).symm a
    apply y.property
    refine ⟨k.val,?_⟩
    apply (slotEquiv bits).injective
    apply Prod.ext
    · exact (leftSlot_rightTime bits H t k.val).trans k.property
    · exact ha⟩⟩
  invFun xy := ⟨joinSlot bits xy.1 xy.2.val,by
    rintro ⟨k,hk⟩
    have he := congrArg (slotEquiv bits) hk
    have hl : leftSlot bits (H.position (rightTime (m:=m) 0) k)=xy.1 := by
      rw [←leftSlot_rightTime bits H t k]
      exact (congrArg Prod.fst he).trans (congrArg Prod.fst ((slotEquiv bits).apply_symm_apply (xy.1,xy.2.val)))
    apply xy.2.property
    refine ⟨Fintype.equivFin (ColumnLabels bits H xy.1) ⟨k,hl⟩,?_⟩
    simp only [columnFamily,Equiv.symm_apply_apply]
    exact (congrArg Prod.snd he).trans (congrArg Prod.snd ((slotEquiv bits).apply_symm_apply (xy.1,xy.2.val)))⟩
  left_inv y := by
    apply Subtype.ext
    exact (slotEquiv bits).symm_apply_apply y.val
  right_inv xy := by
    rcases xy with ⟨x,y⟩
    have he := (slotEquiv bits).apply_symm_apply (x,y.val)
    apply Sigma.ext (congrArg Prod.fst he)
    have hl : leftSlot bits (joinSlot bits x y.val)=x := congrArg Prod.fst he
    apply (Subtype.heq_iff_coe_eq (by
      intro a
      change a∉Set.range ((columnFamily bits H (leftSlot bits (joinSlot bits x y.val))).position t) ↔ _
      rw [hl])).mpr
    exact congrArg Prod.snd he

abbrev RowSamples := ∀y, ConditionalChoices (rowFamily bits H y)
abbrev ColumnSamples := ∀x, ConditionalChoices (columnFamily bits H x)

def rowRemaining (g : RowSamples bits H) : FreeSlot H 0 ≃ FreeSlot H (rightTime (m:=m) 0) :=
  (rowFreeEquiv bits H 0).trans ((Equiv.sigmaCongrRight (fun y =>
    remainingBijection (rowFamily bits H y) (g y).val (g y).property)).trans
    (rowFreeEquiv bits H (Fin.last m)).symm)

def columnRemaining (g : ColumnSamples bits H) :
    FreeSlot H (rightTime (m:=m) 0) ≃ FreeSlot H (Fin.last (m+n)) :=
  (columnFreeEquiv bits H 0).trans ((Equiv.sigmaCongrRight (fun x =>
    remainingBijection (columnFamily bits H x) (g x).val (g x).property)).trans
    (columnFreeEquiv bits H (Fin.last n)).symm)

@[simp] lemma rowRemaining_val (g : RowSamples bits H) (a : FreeSlot H 0) :
    (rowRemaining bits H g a).val = joinSlot bits
      (gridSweep (leftBits bits) (g (rightSlot bits a.val)).val (leftSlot bits a.val))
      (rightSlot bits a.val) := rfl

@[simp] lemma columnRemaining_val (g : ColumnSamples bits H)
    (a : FreeSlot H (rightTime (m:=m) 0)) :
    (columnRemaining bits H g a).val = joinSlot bits (leftSlot bits a.val)
      (gridSweep (rightBits bits) (g (leftSlot bits a.val)).val (rightSlot bits a.val)) := rfl

lemma remainingBijection_split (g : ConditionalChoices H) :
    remainingBijection H g.val g.property =
      (rowRemaining bits H ((conditionalChoicesEquiv bits H g).1)).trans
        (columnRemaining bits H ((conditionalChoicesEquiv bits H g).2)) := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  change gridSweep bits g.val a.val =
    (columnRemaining bits H ((conditionalChoicesEquiv bits H g).2)
      (rowRemaining bits H ((conditionalChoicesEquiv bits H g).1) a)).val
  rw [columnRemaining_val,rowRemaining_val,left_join,right_join]
  apply (slotEquiv bits).injective
  have he := Equiv.congr_fun (gridSweep_split bits g.val) (slotEquiv bits a.val)
  simpa [conditionalChoicesEquiv,Equiv.permCongr_apply,rowPerm,columnPerm,
    slotEquiv] using he

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

def rowReference : FreeSlot H 0 ≃ FreeSlot H (rightTime (m:=m) 0) :=
  (rowFreeEquiv bits H 0).trans ((Equiv.sigmaCongrRight (fun y =>
    freeIdentification (rowFamily bits H y))).trans
    (rowFreeEquiv bits H (Fin.last m)).symm)

def columnReference : FreeSlot H (rightTime (m:=m) 0) ≃ FreeSlot H (Fin.last (m+n)) :=
  (columnFreeEquiv bits H 0).trans ((Equiv.sigmaCongrRight (fun x =>
    freeIdentification (columnFamily bits H x))).trans
    (columnFreeEquiv bits H (Fin.last n)).symm)

def rowRelative (g : RowSamples bits H) : Equiv.Perm (FreeSlot H 0) :=
  (rowRemaining bits H g).trans (rowReference bits H).symm

def columnRelative (g : ColumnSamples bits H) : Equiv.Perm (FreeSlot H (rightTime (m:=m) 0)) :=
  (columnRemaining bits H g).trans (columnReference bits H).symm

def framePermutation : Equiv.Perm (FreeSlot H 0) :=
  ((rowReference bits H).trans (columnReference bits H)).trans (freeIdentification H).symm

theorem remainingPerm_factor (g : ConditionalChoices H) :
    remainingPerm H g.val g.property = framePermutation bits H *
      (rowReference bits H).symm.permCongr
        (columnRelative bits H ((conditionalChoicesEquiv bits H g).2)) *
      rowRelative bits H ((conditionalChoicesEquiv bits H g).1) := by
  unfold remainingPerm
  rw [remainingBijection_split]
  apply Equiv.ext
  intro x
  simp [framePermutation,rowRelative,columnRelative,Equiv.permCongr_apply]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V)

def rowAverage (z : ℝ) : V →ₗ[ℂ] V :=
  ∑g : RowSamples bits H,
    ((∏y, conditionalChoiceWeight (rowFamily bits H y) z (g y)):ℂ) • ρ (rowRelative bits H g)

def columnAverage (z : ℝ) : V →ₗ[ℂ] V :=
  ∑g : ColumnSamples bits H,
    ((∏x, conditionalChoiceWeight (columnFamily bits H x) z (g x)):ℂ) •
      ρ ((rowReference bits H).symm.permCongr (columnRelative bits H g))

omit [FiniteDimensional ℂ V] in
theorem groupAverage_split (z : ℝ) :
    groupAverage ρ (fun a => (conditionalGroupLaw H z a:ℂ)) =
      ρ (framePermutation bits H) * columnAverage bits H ρ z * rowAverage bits H ρ z := by
  rw [groupAverage_conditional,← Equiv.sum_comp (conditionalChoicesEquiv bits H).symm]
  simp_rw [conditionalChoiceWeight_split,remainingPerm_factor,
    Equiv.apply_symm_apply,map_mul,Complex.ofReal_mul]
  rw [Fintype.sum_prod_type]
  unfold columnAverage rowAverage
  simp only [Finset.mul_sum,Finset.sum_mul,smul_mul_assoc,mul_smul_comm,
    Finset.smul_sum,smul_smul,Complex.ofReal_prod]

theorem conditional_evenMoment_split (z : ℝ) (q : ℕ)
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) :
    evenMoment q (groupAverage ρ (fun a => (conditionalGroupLaw H z a:ℂ))) =
      evenMoment q (columnAverage bits H ρ z * rowAverage bits H ρ z) := by
  rw [groupAverage_split,mul_assoc]
  apply evenMoment_unitary_left
  rw [unitary_rep_adjoint ρ hρ,←map_mul,inv_mul_cancel,map_one]

end BinaryCoordinateSweeps.GridSplit

end

end OAI
