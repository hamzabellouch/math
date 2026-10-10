import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

inductive Role
  | word
  | pivot (j:ℕ)
  | anchor (j:ℕ) (big:Bool)
  | filler
  deriving DecidableEq

structure Layout where
  Slot : Type
  finite : Fintype Slot
  role : Slot → Role
  eligible : Slot → Prop

instance (T:Layout) : Fintype T.Slot := T.finite

def Layout.IsPivot (T:Layout) (j:ℕ) (i:T.Slot) : Prop := T.eligible i ∧ T.role i=.pivot j

def Layout.IsCopied (T:Layout) (j:ℕ) (i:T.Slot) : Prop :=
  T.eligible i ∧ (T.role i=.word ∨
    (∃l,j<l ∧ T.role i=.pivot l) ∨ ∃b,T.role i=.anchor j b)

def Layout.IsOutside (T:Layout) (j:ℕ) (i:T.Slot) : Prop := ¬T.IsPivot j i ∧ ¬T.IsCopied j i

def Layout.step (T:Layout) (j:ℕ) : Layout where
  Slot := ({i:T.Slot // T.IsCopied j i} × Bool) ⊕ {i:T.Slot // T.IsOutside j i}
  finite := inferInstance
  role := fun z=>match z with
    | .inl (i,_) => T.role i.val
    | .inr i => T.role i.val
  eligible := fun z=>match z with
    | .inl (i,b) => T.role i.val=.word ∨ (∃l,T.role i.val=.pivot l ∧ b=true)
    | .inr i => T.eligible i.val

theorem pivot_not_copied (T:Layout) (j:ℕ) (i:T.Slot) (h:T.IsPivot j i) : ¬T.IsCopied j i := by
  rintro ⟨_,hw|hp|ha⟩
  · rw [h.2] at hw; contradiction
  · obtain ⟨l,hl,he⟩ := hp
    have : j=l := Role.pivot.inj (h.2.symm.trans he)
    omega
  · obtain ⟨b,hb⟩ := ha
    rw [h.2] at hb; contradiction

theorem word_copied (T:Layout) (j:ℕ) (i:T.Slot)
    (he:T.eligible i) (hw:T.role i=.word) : T.IsCopied j i := ⟨he,Or.inl hw⟩

theorem future_pivot_copied (T:Layout) (j l:ℕ) (hjl:j<l) (i:T.Slot)
    (he:T.eligible i) (hp:T.role i=.pivot l) : T.IsCopied j i :=
  ⟨he,Or.inr (Or.inl ⟨l,hjl,hp⟩)⟩

theorem future_anchor_outside (T:Layout) (j l:ℕ) (hjl:j<l) (b:Bool) (i:T.Slot)
    (ha:T.role i=.anchor l b) : T.IsOutside j i := by
  constructor
  · rintro ⟨_,hp⟩; rw [ha] at hp; contradiction
  · rintro ⟨_,hw|hp|han⟩
    · rw [ha] at hw; contradiction
    · obtain ⟨r,_,hr⟩ := hp; rw [ha] at hr; contradiction
    · obtain ⟨c,hc⟩ := han
      have : l=j := (Role.anchor.inj (ha.symm.trans hc)).1
      omega

def wordEquiv (T:Layout) (j:ℕ) :
    {i:(T.step j).Slot // (T.step j).eligible i ∧ (T.step j).role i=.word} ≃
      {i:T.Slot // T.eligible i ∧ T.role i=.word} × Bool where
  toFun z := by
    rcases z with ⟨z,hz⟩
    cases z with
    | inl q => exact (⟨q.1.val,⟨q.1.property.1,hz.2⟩⟩,q.2)
    | inr q => exact False.elim (q.property.2 (word_copied T j q.val hz.1 hz.2))
  invFun z := ⟨.inl (⟨z.1.val,word_copied T j z.1.val z.1.property.1 z.1.property.2⟩,z.2),
    ⟨Or.inl z.1.property.2,z.1.property.2⟩⟩
  left_inv z := by
    rcases z with ⟨z,hz⟩
    cases z with
    | inl q => rfl
    | inr q => exact False.elim (q.property.2 (word_copied T j q.val hz.1 hz.2))
  right_inv z := rfl

def futurePivotEquiv (T:Layout) (j l:ℕ) (hjl:j<l) :
    {i:(T.step j).Slot // (T.step j).IsPivot l i} ≃ {i:T.Slot // T.IsPivot l i} where
  toFun z := by
    rcases z with ⟨z,hz⟩
    cases z with
    | inl q => exact ⟨q.1.val,q.1.property.1,hz.2⟩
    | inr q => exact False.elim (q.property.2 (future_pivot_copied T j l hjl q.val hz.1 hz.2))
  invFun z := ⟨.inl (⟨z.val,future_pivot_copied T j l hjl z.val z.property.1 z.property.2⟩,true),
    ⟨Or.inr ⟨l,z.property.2,rfl⟩,z.property.2⟩⟩
  left_inv z := by
    rcases z with ⟨z,hz⟩
    cases z with
    | inl q =>
      have hb : q.2=true := by
        rcases hz.1 with hw | ⟨r,hr,hb⟩
        · have he : Role.pivot l=Role.word := hz.2.symm.trans hw
          contradiction
        · exact hb
      apply Subtype.ext
      exact congrArg (fun b=>Sum.inl (q.1,b)) hb.symm
    | inr q => exact False.elim (q.property.2 (future_pivot_copied T j l hjl q.val hz.1 hz.2))
  right_inv z := rfl

def futureAnchorEquiv (T:Layout) (j l:ℕ) (hjl:j<l) (b:Bool) :
    {i:(T.step j).Slot // (T.step j).eligible i ∧ (T.step j).role i=.anchor l b} ≃
      {i:T.Slot // T.eligible i ∧ T.role i=.anchor l b} where
  toFun z := by
    rcases z with ⟨z,hz⟩
    cases z with
    | inl q => exact False.elim ((future_anchor_outside T j l hjl b q.1.val hz.2).2 q.1.property)
    | inr q => exact ⟨q.val,hz.1,hz.2⟩
  invFun z := ⟨.inr ⟨z.val,future_anchor_outside T j l hjl b z.val z.property.2⟩,z.property⟩
  left_inv z := by
    rcases z with ⟨z,hz⟩
    cases z with
    | inl q => exact False.elim ((future_anchor_outside T j l hjl b q.1.val hz.2).2 q.1.property)
    | inr q => rfl
  right_inv z := rfl

end Ostmann.Characters.Template

end

end OAI
