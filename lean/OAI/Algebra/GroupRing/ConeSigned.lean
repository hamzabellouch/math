import Mathlib
import OAI.Algebra.GroupRing.WordCursor
import OAI.Algebra.GroupRing.ConeBoundaryPaths
import OAI.Algebra.GroupRing.ConeChains

namespace OAI



section
namespace TorsionFreeZeroDivisors.ConeSigned
open scoped Classical
open PortSubdivision GraphPresentation GraphConePresentation
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ) (label : D→S×Bool)
def pack : (S×Bool) ⊕ (ConePicture.Radial Γ R × Bool) ≃ (Generator (S:=S) Γ R × Bool) where
  toFun | .inl (s,b)=>(.inl s,b) | .inr (v,b)=>(.inr v,b)
  invFun | (.inl s,b)=>.inl (s,b) | (.inr v,b)=>.inr (v,b)
  left_inv x := by rcases x with ⟨s,b⟩|⟨v,b⟩ <;> rfl
  right_inv x := by rcases x with ⟨s|v,b⟩ <;> rfl
lemma pack_inverse (a : (S×Bool) ⊕ (ConePicture.Radial Γ R × Bool)) :
    pack (S:=S) Γ R (ConePicture.inverse Γ R WordPairing.inverseLetter a)=
      WordPairing.inverseLetter (pack Γ R a) := by
  rcases a with ⟨s,b⟩|⟨v,b⟩ <;> rfl
def labels : ConePicture.Dart Γ R→Generator (S:=S) Γ R × Bool := pack Γ R ∘ ConePicture.labels Γ R label
lemma labels_reverse (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
    (d : ConePicture.Dart Γ R) :
    labels Γ R label ((ConePicture.graph Γ R).reverse d)=WordPairing.inverseLetter (labels Γ R label d) := by
  dsimp only [labels,Function.comp_apply]
  rw [ConePicture.label_reverse Γ R label WordPairing.inverseLetter hl,pack_inverse]
def unpack {O : Type}[Fintype O]
    (a : SphericalPicture.Data (O:=O) (ConePicture.graph Γ R) (labels Γ R label) WordPairing.inverseLetter) :
    SphericalPicture.Data (O:=O) (ConePicture.graph Γ R) (ConePicture.labels Γ R label)
      (ConePicture.inverse Γ R WordPairing.inverseLetter) where
  rotation := a.rotation
  partner := a.partner
  involutive := a.involutive
  fixed_free := a.fixed_free
  dart := a.dart
  consistent := a.consistent
  compatible i := by
    apply (pack Γ R).injective
    rw [pack_inverse]
    exact a.compatible i
  genusZero := a.genusZero
lemma reduces_to_empty (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (a : SphericalPicture.Data (O:=P) Γ label WordPairing.inverseLetter),¬a.Reduced)
    {O : Type}[Fintype O]
    (a : SphericalPicture.Data (O:=O) (ConePicture.graph Γ R) (labels Γ R label) WordPairing.inverseLetter) :
    SphericalPicture.ReducesToEmpty _ _ _ a := by
  apply SphericalPicture.reduces_of_no_reduced WordPairing.inverseLetter_involutive (labels_reverse Γ R label hl)
  intro P _ _ b hb
  exact hex (ConePicture.oldData (unpack Γ R label b) hb)
    (ConePicture.oldData_reduced _ hb)
def freeLetter {A : Type} (a : A×Bool) : FreeGroup A := FreeGroup.mk [a]
lemma freeLetter_inverse {A : Type} (a : A×Bool) :
    freeLetter (WordPairing.inverseLetter a)=(freeLetter a)⁻¹ := by
  change FreeGroup.mk [WordPairing.inverseLetter a]=(FreeGroup.mk [a])⁻¹
  rw [FreeGroup.inv_mk]
  rfl
lemma freeLetter_map {A B : Type} (f : A→B) (a : A×Bool) :
    FreeGroup.map f (freeLetter a)=freeLetter (f a.1,a.2) := by
  simp only [freeLetter,FreeGroup.map.mk,List.map_singleton]
local notation "letters" => freeLetter ∘ label
local notation "G" => GraphConePresentation.Group Γ letters R
def eval (a : Generator (S:=S) Γ R × Bool) : G := PresentedGroup.mk _ (freeLetter a)
lemma eval_inverse (a : Generator (S:=S) Γ R × Bool) :
    eval Γ R label (WordPairing.inverseLetter a)=(eval Γ R label a)⁻¹ := by
  simp only [eval,freeLetter_inverse,map_inv]
lemma eval_pack (a : (S×Bool) ⊕ (ConePicture.Radial Γ R × Bool)) :
    eval Γ R label (pack Γ R a)=ConeChains.eval Γ R label freeLetter a := by
  rcases a with ⟨s,b⟩|⟨v,b⟩
  · change PresentedGroup.mk _ (freeLetter (Sum.inl s,b))=
      oldMap Γ letters R (freeLetter (s,b))
    rw [oldMap,MonoidHom.comp_apply,old,freeLetter_map]
  · cases b
    · change PresentedGroup.mk _ (FreeGroup.of (Sum.inr v))⁻¹=
        (radialValue Γ letters R v)⁻¹
      rw [map_inv,radialValue,radial,dite_eq_right v.property]
    · change PresentedGroup.mk _ (FreeGroup.of (Sum.inr v))=radialValue Γ letters R v
      rw [radialValue,radial,dite_eq_right v.property]
lemma wordLabel_eq (d : ConePicture.Dart Γ R) :
    freeLetter (labels Γ R label d)=ConePicture.wordLabel Γ R letters d := by
  rcases d with d|⟨v,b⟩
  · change freeLetter (Sum.inl (label d).1,(label d).2)=FreeGroup.map Sum.inl (freeLetter (label d))
    exact (freeLetter_map _ _).symm
  · cases b <;> rfl
lemma value_mk {A H : Type} [Group H] (q : FreeGroup A→*H) (w : List (A×Bool)) :
    WordCursor.value (fun a=>q (freeLetter a)) w=q (FreeGroup.mk w) := by
  induction w with
  | nil=>exact (map_one q).symm
  | cons a w ih=>rw [WordCursor.value_cons,ih,show a::w=[a]++w from rfl,←FreeGroup.mul_mk,map_mul];rfl
lemma eval_value (w : List (Generator (S:=S) Γ R × Bool)) :
    WordCursor.value (eval Γ R label) w=PresentedGroup.mk _ (FreeGroup.mk w) :=
  value_mk _ w

end
end TorsionFreeZeroDivisors.ConeSigned

end


end OAI
