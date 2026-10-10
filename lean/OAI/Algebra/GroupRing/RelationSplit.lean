import Mathlib
import OAI.Algebra.GroupRing.RelationArea

namespace OAI



section
namespace TorsionFreeZeroDivisors.RelationSplit
open scoped Classical BigOperators
open AlgebraicPictures CellModule RelationArea
noncomputable section
variable {A I : Type} (rel : I→List (A×Bool))
variable (hz : ∀ts : List (Term (A:=A) (I:=I)),FreeGroup.mk (word rel ts)=1→total rel ts=0)
def sectionWord (g : G rel) : FreeGroup A := Classical.choose (PresentedGroup.mk_surjective (relations rel) g)
lemma sectionWord_q (g : G rel) : q rel (sectionWord rel g)=g :=
  Classical.choose_spec (PresentedGroup.mk_surjective (relations rel) g)
def loop (g : G rel) (w : FreeGroup A) : N rel :=
  ⟨sectionWord rel g*w*(sectionWord rel (g*q rel w))⁻¹,PresentedGroup.mk_eq_one_iff.mp (by
    simp only [map_mul,map_inv,sectionWord_q,mul_inv_cancel])⟩
lemma loop_one (g : G rel) : loop rel g 1=1 := by
  apply Subtype.ext
  simp [loop]
lemma loop_mul (g : G rel) (w u : FreeGroup A) :
    loop rel g (w*u)=loop rel g w*loop rel (g*q rel w) u := by
  apply Subtype.ext
  simp only [loop,Subgroup.coe_mul,map_mul,mul_assoc]
  group
include hz in
lemma area_loop_mul (g : G rel) (w u : FreeGroup A) :
    area rel (loop rel g (w*u))=area rel (loop rel g w)+area rel (loop rel (g*q rel w) u) := by
  rw [loop_mul,area_mul rel hz]
include hz in
lemma area_loop_inv (g : G rel) (w : FreeGroup A) :
    area rel (loop rel g w⁻¹)= -area rel (loop rel (g*(q rel w)⁻¹) w) := by
  have h := area_loop_mul rel hz g w⁻¹ w
  rw [inv_mul_cancel,loop_one,area_one rel hz,map_inv] at h
  exact eq_neg_of_add_eq_zero_left h.symm

def retract : CellModule.Module (G rel) A→+CellModule.Module (G rel) I :=
  Finsupp.liftAddHom (fun p=>zmultiplesHom _ (area rel (loop rel p.1 (FreeGroup.of p.2))))
@[simp] lemma retract_single (p : G rel×A) (z : ℤ) :
    retract rel (Finsupp.single p z)=z • area rel (loop rel p.1 (FreeGroup.of p.2)) := by
  simp [retract]
include hz in
lemma retract_fox (w : FreeGroup A) (g : G rel) :
    retract rel (translate g (fox (q rel) w))=area rel (loop rel g w) := by
  induction w using FreeGroup.induction_on generalizing g with
  | one=>rw [fox_one,map_zero,map_zero,loop_one,area_one rel hz]
  | of a=>simp only [fox_of,translate_single,mul_one,retract_single,one_zsmul]
  | inv_of a ih=>
    rw [fox_inv,map_neg,map_neg,←translate_mul,ih,area_loop_inv rel hz]
  | mul w u hw hu=>
    rw [fox_mul,map_add,map_add,←translate_mul,hw,hu,area_loop_mul rel hz]
include hz in
lemma area_rel (i : I) : area rel ⟨FreeGroup.mk (rel i),Subgroup.subset_normalClosure ⟨i,rfl⟩⟩=
    Finsupp.single (1,i) 1 := by
  let t : Term (A:=A) (I:=I) := ⟨i,true,[]⟩
  have ht : FreeGroup.mk (word rel [t])=FreeGroup.mk (rel i) := by
    simp [word,Term.word,Term.core,t]
  rw [area_eq rel hz _ [t] ht]
  simp [total,term,t,←FreeGroup.one_eq_mk]
include hz in
lemma retract_d₂_single (g : G rel) (i : I) :
    retract rel (d₂ rel (Finsupp.single (g,i) 1))=Finsupp.single (g,i) 1 := by
  rw [d₂_single,one_zsmul,retract_fox rel hz]
  have he : loop rel g (FreeGroup.mk (rel i))=
      conjugate rel (sectionWord rel g) ⟨FreeGroup.mk (rel i),Subgroup.subset_normalClosure ⟨i,rfl⟩⟩ := by
    apply Subtype.ext
    simp only [loop,conjugate,q_rel,mul_one]
  rw [he,area_conjugate rel hz,area_rel rel hz,sectionWord_q,translate_single,mul_one]
include hz in
/-- The actual integral physical-cell boundary is a split injection as an
abelian-group map. The splitting uses genuine normal-closure expansions,
not a hypothesis of cellular acyclicity. -/
lemma retract_d₂ (x : CellModule.Module (G rel) I) : retract rel (d₂ rel x)=x := by
  induction x using Finsupp.induction_linear with
  | zero=>simp
  | add a b ha hb=>simp only [map_add,ha,hb]
  | single p z=>
    have hs : Finsupp.single p z=z • Finsupp.single p (1:ℤ) := by simp
    rw [hs,map_zsmul,map_zsmul,retract_d₂_single rel hz p.1 p.2]
include hz in
lemma d₂_injective : Function.Injective (d₂ rel) :=
  Function.LeftInverse.injective (retract_d₂ rel hz)
end
end TorsionFreeZeroDivisors.RelationSplit

end


end OAI
