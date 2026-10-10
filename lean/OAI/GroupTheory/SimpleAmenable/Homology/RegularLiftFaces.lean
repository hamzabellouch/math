import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.RegularBlock
import OAI.GroupTheory.SimpleAmenable.Simplicial.MonoidFaceLabels

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite
namespace RegularCoordinates
open CoefficientNerve MonoidNerveCoordinates

variable {P:Type} [CommMonoid P]
lemma trunc_lift {m n:ℕ} (f:⦋m⦌⟶⦋n⦌) (p:P) (s:B (P:=P) n) :
    trunc f (lift p s)=lift (tail f s * p) (trunc f s) := by
  apply (coordinates m).injective
  apply Prod.ext
  · change (trunc f (lift p s)).right.unop.back=(lift _ _).right.unop.back
    rw [lift_right]
    rfl
  · change trunc f (lift p s) ⋙ (ActionCategory.π P P).op=lift _ _ ⋙ (ActionCategory.π P P).op
    rw [lift_project]
    change (SimplexCategory.toCat.map f).toFunctor ⋙ (lift p s ⋙ (ActionCategory.π P P).op)=_
    erw [lift_project]
    rfl
noncomputable def arrow (a p:P) : ActionCategory.objEquiv P P p ⟶ ActionCategory.objEquiv P P (a*p) := ⟨a,rfl⟩
lemma arrow_one (p:P) : arrow (1:P) p=eqToHom (congrArg (ActionCategory.objEquiv P P) (one_mul p).symm) := by
  apply Functor.Elements.Hom.ext
  exact (RegularTranslation.eqToHom_val _).symm
end RegularCoordinates
namespace RegularLabels
open CoefficientNerve RegularCoordinates MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ FreeChains.A)
noncomputable def singleLabel {n:ℕ} (p:P) (y:Fin n→P) : fiber F p ⟶ Obj F n :=
  eqToHom (congrArg F.obj (rightEq p y).symm) ≫ single F (lift p (ofLabels y))
lemma singleLabel_map_general {m n:ℕ} (f:⦋m⦌⟶⦋n⦌) (p:P) (y:Fin n→P) :
    singleLabel F p y ≫ map F f =
      F.map (arrow (tail f (ofLabels y)) p) ≫
        singleLabel F (tail f (ofLabels y)*p) (labels (trunc f (ofLabels y))) := by
  dsimp only [singleLabel]
  rw [←eqToHom_map F (rightEq p y).symm,
    ←eqToHom_map F (rightEq (tail f (ofLabels y)*p) (labels (trunc f (ofLabels y)))).symm]
  simp only [Category.assoc,single_map,←F.map_comp_assoc]
  apply weighted_eq F (by rw [trunc_lift,ofLabels_labels])
  apply Functor.Elements.Hom.ext
  simp only [ActionCategory.comp_hom,RegularTranslation.eqToHom_val,one_mul,mul_one]
  rfl
noncomputable def faceWeight {n:ℕ} (k:Fin (n+2)) (y:Fin (n+1)→P) : P :=
  if k=Fin.last (n+1) then y (Fin.last n) else 1
lemma tail_face {n:ℕ} (k:Fin (n+2)) (y:Fin (n+1)→P) :
    tail (SimplexCategory.δ k) (ofLabels y)=faceWeight k y := by
  dsimp only [faceWeight]
  split_ifs with h
  · subst k
    exact (tail_face_last_val (ofLabels y)).trans (congrFun (labels_ofLabels y) (Fin.last n))
  · exact tail_face_val (ofLabels y) k h
@[reassoc] lemma singleLabel_face {n:ℕ} (k:Fin (n+2)) (p:P) (y:Fin (n+1)→P) :
    singleLabel F p y ≫ (simplicial F).δ k =
      F.map (arrow (faceWeight k y) p) ≫
        singleLabel F (faceWeight k y*p) (faceLabels k y) := by
  change singleLabel F p y ≫ map F (SimplexCategory.δ k)=_
  rw [singleLabel_map_general,tail_face]
  congr 2
  exact (labels_face (ofLabels y) k).trans (congrArg (faceLabels k) (labels_ofLabels y))
@[reassoc] lemma singleLabel_action (a p:P) {n:ℕ} (y:Fin n→P) :
    singleLabel F p y ≫ (RegularCoefficient.action F a).app (op ⦋n⦌) =
      F.map (arrow a p) ≫ singleLabel F (a*p) y := by
  dsimp only [singleLabel]
  rw [←eqToHom_map F (rightEq p y).symm,←eqToHom_map F (rightEq (a*p) y).symm]
  erw [Category.assoc,RegularCoefficient.single_action]
  erw [←F.map_comp_assoc,←F.map_comp_assoc]
  apply weighted_eq F (shift_lift a p (ofLabels y))
  apply Functor.Elements.Hom.ext
  simp only [ActionCategory.comp_hom,RegularTranslation.eqToHom_val,one_mul,mul_one]
  rfl
end RegularLabels

end

end OAI
