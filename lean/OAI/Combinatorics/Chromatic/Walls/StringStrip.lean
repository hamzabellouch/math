import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SignedMultiplicity

namespace OAI

section
namespace ElementaryPositivity.SignedMultiplicity
noncomputable section
variable {A B : Type*} (evenA : A → Prop) (evenB : B → Prop)

def countSumEquiv : CountSelection (Sum.elim evenA evenB) ≃
    CountSelection evenA × CountSelection evenB where
  toFun f:=⟨⟨(Finsupp.sumFinsuppEquivProdFinsupp f.val).1,fun a ha=>f.property (.inl a) ha⟩,
    ⟨(Finsupp.sumFinsuppEquivProdFinsupp f.val).2,fun b hb=>f.property (.inr b) hb⟩⟩
  invFun fg:=⟨fg.1.val.sumElim fg.2.val,by
    intro x hx
    cases x with
    | inl a=>exact fg.1.property a hx
    | inr b=>exact fg.2.property b hx⟩
  left_inv f:=by
    apply Subtype.ext
    exact Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply f.val
  right_inv fg:=by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply (fg.1.val,fg.2.val))
    · apply Subtype.ext
      exact congrArg Prod.snd (Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply (fg.1.val,fg.2.val))

lemma countSum_sum {T : Type*} [AddCommMonoid T]
    (f : CountSelection (Sum.elim evenA evenB)) (e : A ⊕ B → T) :
    f.val.sum (fun x n=>n • e x)=
      ((countSumEquiv evenA evenB f).1).val.sum (fun a n=>n • e (.inl a))+
      ((countSumEquiv evenA evenB f).2).val.sum (fun b n=>n • e (.inr b)) := by
  have H:=Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply f.val
  change ((Finsupp.sumFinsuppEquivProdFinsupp f.val).1.sumElim
    (Finsupp.sumFinsuppEquivProdFinsupp f.val).2)=f.val at H
  conv_lhs=>rw [←H]
  exact Finsupp.sum_sumElim _ _ _
end
end ElementaryPositivity.SignedMultiplicity

namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity
noncomputable section
variable {S : Type*} (a : S → ℕ) (t : S → ℕ)

abbrev HeadLevel := Σs,Fin (t s)

def levelCutEquiv : S×ℕ ≃ HeadLevel t ⊕ (S×ℕ) where
  toFun x:=if h:x.2<t x.1 then .inl ⟨x.1,⟨x.2,h⟩⟩ else .inr (x.1,x.2-t x.1)
  invFun x:=Sum.elim (fun x : HeadLevel t=>(x.1,x.2.val))
    (fun x : S×ℕ=>(x.1,x.2+t x.1)) x
  left_inv x:=by
    dsimp only
    split_ifs with h
    · rfl
    · change (x.1,x.2-t x.1+t x.1)=x
      exact Prod.ext rfl (Nat.sub_add_cancel (Nat.le_of_not_gt h))
  right_inv x:=by
    cases x with
    | inl x=>
      dsimp only [Sum.elim_inl]
      rw [dite_eq_left x.2.isLt]
    | inr x=>
      dsimp only [Sum.elim_inr]
      rw [dite_eq_right (show ¬x.2+t x.1<t x.1 by omega),Nat.add_sub_cancel_right]

lemma levelCut_even (x : S×ℕ) :
    (a x.1≠0) ↔ Sum.elim (fun x : HeadLevel t=>a x.1≠0)
      (fun x : S×ℕ=>a x.1≠0) (levelCutEquiv t x) := by
  dsimp only [levelCutEquiv,Equiv.coe_fn_mk]
  split_ifs <;> rfl

def stringStripEquiv : CountSelection (fun x : S×ℕ=>a x.1≠0) ≃
    CountSelection (fun x : HeadLevel t=>a x.1≠0) ×
      CountSelection (fun x : S×ℕ=>a x.1≠0) :=
  (countReindex (levelCutEquiv t) _ _ (levelCut_even a t)).trans
    (countSumEquiv _ _)

lemma stringStrip_sum {T : Type*} [AddCommMonoid T]
    (f : CountSelection (fun x : S×ℕ=>a x.1≠0)) (e : S×ℕ → T) :
    f.val.sum (fun x n=>n • e x)=
      (stringStripEquiv a t f).1.val.sum (fun x n=>n • e (x.1,x.2.val))+
      (stringStripEquiv a t f).2.val.sum (fun x n=>n • e (x.1,x.2+t x.1)) := by
  have H:=countReindex_sum (levelCutEquiv t) _ _ (levelCut_even a t) f
    (fun x=>e ((levelCutEquiv t).symm x))
  simp only [Equiv.symm_apply_apply] at H
  rw [←H,countSum_sum]
  rfl

lemma stringStrip_dimension {T : Type*} [AddCommMonoid T] (dim : S → T)
    (f : CountSelection (fun x : S×ℕ=>a x.1≠0)) :
    f.val.sum (fun x n=>n • dim x.1)=
      (stringStripEquiv a t f).1.val.sum (fun x n=>n • dim x.1)+
      (stringStripEquiv a t f).2.val.sum (fun x n=>n • dim x.1) :=
  stringStrip_sum a t f (fun x=>dim x.1)

lemma stringStrip_energy (k : S → ℤ)
    (f : CountSelection (fun x : S×ℕ=>a x.1≠0)) :
    f.val.sum (fun x n=>n • (k x.1+2*(t x.1:ℤ)-2*(x.2:ℤ)))=
      (stringStripEquiv a t f).1.val.sum (fun x n=>n • (k x.1+2*(t x.1:ℤ)-2*(x.2.val:ℤ)))+
      (stringStripEquiv a t f).2.val.sum (fun x n=>n • (k x.1-2*(x.2:ℤ))) := by
  rw [stringStrip_sum]
  congr 1
  apply Finsupp.sum_congr
  intro x hx
  congr 1
  simp only [Nat.cast_add]
  ring
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.SignedMultiplicity
noncomputable section
variable {S I : Type*} (even : S → Prop) (dim : S → (I → ℕ))

def countDimension (f : CountSelection even) : I → ℕ :=
  f.val.sum (fun s n=>n • dim s)

def zeroCount : CountSelection even := ⟨0,by simp⟩

@[simp] lemma countDimension_zero : countDimension even dim (zeroCount even)=0 := by
  simp [countDimension,zeroCount]

lemma countDimension_apply (f : CountSelection even) (i : I) :
    countDimension even dim f i=∑s∈f.val.support,f.val s*dim s i := by
  simp [countDimension,Finsupp.sum,Finset.sum_apply]

lemma count_eq_zero_of_dimension (hdim : ∀s,dim s≠0) (f : CountSelection even)
    (h : countDimension even dim f=0) : f=zeroCount even := by
  classical
  apply Subtype.ext
  ext s
  by_contra H
  have hs : s∈f.val.support := Finsupp.mem_support_iff.mpr (by simpa [zeroCount] using H)
  obtain ⟨i,hi⟩:=Function.ne_iff.mp (hdim s)
  have HE:=congrArg (fun d : I→ℕ=>d i) h
  rw [countDimension_apply] at HE
  have HB : f.val s*dim s i≤0 :=
    (Finset.single_le_sum (fun _ _=>Nat.zero_le _) hs).trans_eq HE
  have hf : 0<f.val s := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs)
  have hd : 0<dim s i := Nat.pos_of_ne_zero hi
  exact (not_lt_of_ge HB) (Nat.mul_pos hf hd)

abbrev DimensionCounts (d : I → ℕ) := {f : CountSelection even // countDimension even dim f=d}

include dim in
lemma dimensionCounts_zero_subsingleton (hdim : ∀s,dim s≠0) :
    Subsingleton (DimensionCounts even dim 0) := by
  constructor
  intro f g
  apply Subtype.ext
  exact (count_eq_zero_of_dimension even dim hdim f.val f.property).trans
    (count_eq_zero_of_dimension even dim hdim g.val g.property).symm

def countEnergy (e : S → ℤ) (f : CountSelection even) : ℤ := f.val.sum (fun s n=>n • e s)

@[simp] lemma countEnergy_zero (e : S → ℤ) : countEnergy even e (zeroCount even)=0 := by
  simp [countEnergy,zeroCount]

lemma dimensionCounts_zero_energy (hdim : ∀s,dim s≠0) (e : S → ℤ)
    (f : DimensionCounts even dim 0) : countEnergy even e f.val=0 := by
  rw [count_eq_zero_of_dimension even dim hdim f.val f.property,countEnergy_zero]

lemma countDimension_mem (D : AddSubmonoid (I → ℕ)) (hd : ∀s,dim s∈D) (f : CountSelection even) :
    countDimension even dim f∈D := by
  unfold countDimension Finsupp.sum
  exact D.sum_mem (fun s hs=>D.nsmul_mem (hd s) _)

lemma countEnergy_shift (τ : (I→ℕ) →+ ℤ) (e : S → ℤ) (f : CountSelection even) :
    countEnergy even (fun s=>e s+τ (dim s)) f=
      countEnergy even e f+τ (countDimension even dim f) := by
  simp only [countEnergy,countDimension,Finsupp.sum,map_sum,map_nsmul,smul_add,Finset.sum_add_distrib]
end
end ElementaryPositivity.SignedMultiplicity

end

end OAI
