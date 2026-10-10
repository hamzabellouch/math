import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.LabelledMonoidal
import OAI.GroupTheory.SimpleAmenable.Simplicial.FiniteSetMonoidal
import OAI.GroupTheory.SimpleAmenable.Configurations.StageOrder

namespace OAI

section
open CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.Cell

variable {a n : ℕ} (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n)

noncomputable abbrev object (U : FiniteSetGroupoid) : Labelled a n :=
  ⟨⟨U.size,fun _ => P⟩,fun _ => l.val,fun _ => l.property⟩
noncomputable def pointMap {U V : FiniteSetGroupoid} (f : U ⟶ V) :
    (object P l U).polygon.Point ≃ (object P l V).polygon.Point where
  toFun x := ⟨(f x.val.1,x.val.2),x.property⟩
  invFun y := ⟨(f.symm y.val.1,y.val.2),y.property⟩
  left_inv x := by apply Subtype.ext; exact Prod.ext (f.symm_apply_apply _) rfl
  right_inv y := by apply Subtype.ext; exact Prod.ext (f.apply_symm_apply _) rfl
noncomputable def arrow {U V : FiniteSetGroupoid} (f : U ⟶ V) : object P l U ⟶ object P l V where
  arrow := relabelArrow (pointMap P l f) f (fun _ => rfl)
  positional _ := rfl
  labelled _ := rfl
noncomputable def functor : FiniteSetGroupoid ⥤ Labelled a n where
  obj := object P l
  map := arrow P l
  map_id _ := by apply Hom.ext; apply Arrow.ext; apply Equiv.ext; intro x; rfl
  map_comp _ _ := by apply Hom.ext; apply Arrow.ext; apply Equiv.ext; intro x; rfl
@[simp] lemma arrow_apply {U V : FiniteSetGroupoid} (f : U ⟶ V)
    (x : (object P l U).polygon.Point) :
    ((arrow P l f).arrow.toEquiv x).val = (f x.val.1,x.val.2) := rfl

noncomputable def tensorPoint (U V : FiniteSetGroupoid) :
    (sum (object P l U) (object P l V)).polygon.Point ≃ (object P l (U⊗V)).polygon.Point where
  toFun x := ⟨x.val,by
    obtain ⟨y,rfl⟩ := (sumPointEquiv (object P l U).polygon (object P l V).polygon).surjective x
    cases y with
    | inl y => simpa only [sumPointEquiv_inl,object] using y.property
    | inr y => simpa only [sumPointEquiv_inr,object] using y.property⟩
  invFun x := ⟨x.val,by
    change x.val.2 ∈ (Fin.addCases (motive := fun _ => polygonAlgebra a)
      (fun _ => P) (fun _ => P) x.val.1).val
    refine Fin.addCases (motive := fun i => x.val.2 ∈ (Fin.addCases
      (motive := fun _ => polygonAlgebra a) (fun _ => P) (fun _ => P) i).val)
      (fun i => ?_) (fun i => ?_) x.val.1
    · simpa only [Fin.addCases_left,object] using x.property
    · simpa only [Fin.addCases_right,object] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def tensorArrow (U V : FiniteSetGroupoid) :
    (object P l U) ⊗ (object P l V) ⟶ object P l (U⊗V) where
  arrow := relabelArrow (tensorPoint P l U V) id (fun _ => rfl)
  positional _ := rfl
  labelled x := by
    change l.val = Fin.addCases (fun _ => l.val) (fun _ => l.val) x.val.1
    refine Fin.addCases (motive := fun i => l.val = Fin.addCases
      (motive := fun _ => Fin n → CutRing × CutRing) (fun _ => l.val) (fun _ => l.val) i)
      (fun i => ?_) (fun i => ?_) x.val.1
    · simp only [Fin.addCases_left]
    · simp only [Fin.addCases_right]
@[simp] lemma tensorArrow_apply (U V : FiniteSetGroupoid)
    (x : (sum (object P l U) (object P l V)).polygon.Point) :
    ((tensorArrow P l U V).arrow.toEquiv x).val=x.val := rfl
noncomputable def unitArrow : 𝟙_ (Labelled a n) ⟶ object P l (𝟙_ FiniteSetGroupoid) where
  arrow := relabelArrow {
    toFun x := Fin.elim0 x.val.1
    invFun x := Fin.elim0 x.val.1
    left_inv x := Fin.elim0 x.val.1
    right_inv x := Fin.elim0 x.val.1 } Fin.elim0 (fun x => Fin.elim0 x.val.1)
  positional x := Fin.elim0 x.val.1
  labelled x := Fin.elim0 x.val.1

end SimpleAmenable.PolygonObject.Labelled.Cell

end

end OAI
