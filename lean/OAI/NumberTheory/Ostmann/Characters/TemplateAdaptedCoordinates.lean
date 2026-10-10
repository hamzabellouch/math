import OAI.NumberTheory.Ostmann.Characters.ResidueDivision
import OAI.NumberTheory.Ostmann.Characters.TemplateWords

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def coordinateChild {R:Type*} (k j:ℕ) (b:Bool) (x:(schedule k (j+1)).Slot→R) (P:R) :
    (schedule k j).Slot→R := fun i=>
  if hp:(schedule k j).IsPivot j i then P
  else if hc:(schedule k j).IsCopied j i then x (.inl (⟨i,hc⟩,b))
  else x (.inr ⟨i,⟨hp,hc⟩⟩)

theorem coordinateChild_map {R S:Type*} (f:R→S) (k j:ℕ) (b:Bool)
    (x:(schedule k (j+1)).Slot→R) (P:R) :
    (fun i=>f (coordinateChild k j b x P i))=coordinateChild k j b (fun i=>f (x i)) (f P) := by
  funext i
  unfold coordinateChild
  split_ifs <;> rfl

def installWords {R:Type*} [Monoid R] (k j:ℕ) (C:(schedule k j).Slot→R)
    (z:WordSlot k j→R) : (schedule k j).Slot→R := fun i=>
  C i*(if hw:(schedule k j).eligible i ∧ (schedule k j).role i=.word then z ⟨i,hw⟩ else 1)

def splitWords {R:Type*} (k j:ℕ) (b:Bool) (z:WordSlot k (j+1)→R) : WordSlot k j→R :=
  fun i=>z ((wordEquiv (schedule k j) j).symm (i,b))

theorem coordinateChild_installWords {R:Type*} [Monoid R] (k j:ℕ) (b:Bool)
    (C:(schedule k (j+1)).Slot→R) (z:WordSlot k (j+1)→R) (P:R) :
    coordinateChild k j b (installWords k (j+1) C z) P=
      installWords k j (coordinateChild k j b C P) (splitWords k j b z) := by
  funext i
  by_cases hp:(schedule k j).IsPivot j i
  · have hw : ¬((schedule k j).eligible i ∧ (schedule k j).role i=.word) := by
      rintro ⟨_,hw⟩
      rw [hp.2] at hw
      contradiction
    simp only [coordinateChild,dite_eq_left hp,installWords,dite_eq_right hw,mul_one]
  · by_cases hc:(schedule k j).IsCopied j i
    · by_cases hw:(schedule k j).role i=.word
      · have hwold : (schedule k j).eligible i ∧ (schedule k j).role i=.word := ⟨hc.1,hw⟩
        have hwnew : (schedule k (j+1)).eligible (.inl (⟨i,hc⟩,b)) ∧
            (schedule k (j+1)).role (.inl (⟨i,hc⟩,b))=.word := ⟨Or.inl hw,hw⟩
        simp only [coordinateChild,dite_eq_right hp,dite_eq_left hc,installWords,
          dite_eq_left hwold,dite_eq_left hwnew]
        rfl
      · have hwold : ¬((schedule k j).eligible i ∧ (schedule k j).role i=.word) := fun h=>hw h.2
        have hwnew : ¬((schedule k (j+1)).eligible (.inl (⟨i,hc⟩,b)) ∧
            (schedule k (j+1)).role (.inl (⟨i,hc⟩,b))=.word) := fun h=>hw h.2
        simp only [coordinateChild,dite_eq_right hp,dite_eq_left hc,installWords,
          dite_eq_right hwold,dite_eq_right hwnew,mul_one]
    · have hwold : ¬((schedule k j).eligible i ∧ (schedule k j).role i=.word) :=
        fun h=>hc (word_copied _ _ _ h.1 h.2)
      have hwnew : ¬((schedule k (j+1)).eligible (.inr ⟨i,⟨hp,hc⟩⟩) ∧
          (schedule k (j+1)).role (.inr ⟨i,⟨hp,hc⟩⟩)=.word) := hwold
      simp only [coordinateChild,dite_eq_right hp,dite_eq_right hc,installWords,
        dite_eq_right hwold,dite_eq_right hwnew,mul_one]

def blockProduct {R:Type*} [CommMonoid R] (k j:ℕ) (b:Bool)
    (x:(schedule k (j+1)).Slot→R) : R :=
  ∏i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i},x (.inl (i,b))

theorem blockProduct_map {R S:Type*} [CommMonoid R] [CommMonoid S] (f:R→*S)
    (k j:ℕ) (b:Bool) (x:(schedule k (j+1)).Slot→R) :
    f (blockProduct k j b x)=blockProduct k j b (fun i=>f (x i)) := map_prod f _ _

def copiedWordEquiv (k j:ℕ) :
    {i:{i:(schedule k j).Slot // (schedule k j).IsCopied j i} //
      (schedule k j).role i.val=.word} ≃ WordSlot k j where
  toFun i:=⟨i.val.val,i.val.property.1,i.property⟩
  invFun i:=⟨⟨i.val,word_copied _ _ _ i.property.1 i.property.2⟩,i.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

end Ostmann.Characters.Template

end

end OAI
