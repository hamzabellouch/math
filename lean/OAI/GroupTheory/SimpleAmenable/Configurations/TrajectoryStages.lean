import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.BooleanStages

namespace OAI

section

section

open CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

structure FiniteSetGroupoid where
  size : ℕ
namespace FiniteSetGroupoid
instance : Groupoid FiniteSetGroupoid where
  Hom U V := Fin U.size ≃ Fin V.size
  id object := Equiv.refl (Fin object.size)
  comp f g := f.trans g
  inv f := f.symm
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  inv_comp f := Equiv.symm_trans_self f
  comp_inv f := Equiv.self_trans_symm f
end FiniteSetGroupoid

namespace LabelledStage
variable {a n s : ℕ} (P : BooleanPartition a)
    (L : Fin s → Fin n → CutRing × CutRing)
    (hL : ∀ j i, orbitRepresentative (L j i)=L j i)

abbrev Obj := (Fin P.size × Fin s) → FiniteSetGroupoid
abbrev Track (U : Obj P (s:=s)) := Σ b : Fin P.size × Fin s, Fin (U b).size
noncomputable abbrev index (U : Obj P (s:=s)) := Fintype.equivFin (Track P U)
noncomputable def object (U : Obj P (s:=s)) : Labelled a n where
  polygon := ⟨Fintype.card (Track P U), fun j => P.cell (((index P U).symm j).1.1)⟩
  label j := L (((index P U).symm j).1.2)
  reduced track := hL (((index P U).symm track).1.2)

noncomputable def trackMap {U V : Obj P (s:=s)} (f : U ⟶ V) : Track P U ≃ Track P V :=
  Equiv.sigmaCongrRight f
noncomputable def indexMap {U V : Obj P (s:=s)} (f : U ⟶ V) :
    Fin (object P L hL U).polygon.tracks ≃ Fin (object P L hL V).polygon.tracks :=
  (index P U).symm.trans ((trackMap P f).trans (index P V))

@[simp] theorem indexMap_atom {U V : Obj P (s:=s)} (f : U ⟶ V)
    (j : Fin (object P L hL U).polygon.tracks) :
    ((index P V).symm (indexMap P L hL f j)).1 = ((index P U).symm j).1 := by
  change ((index P V).symm ((index P V) ((trackMap P f) ((index P U).symm j)))).1 = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem indexMap_id (U : Obj P (s:=s)) (j : Fin (object P L hL U).polygon.tracks) :
    indexMap P L hL (𝟙 U) j=j := by
  change (index P U) ((index P U).symm j)=j
  exact Equiv.apply_symm_apply _ _

@[simp] theorem indexMap_comp {U V W : Obj P (s:=s)} (f : U ⟶ V) (g : V ⟶ W)
    (j : Fin (object P L hL U).polygon.tracks) :
    indexMap P L hL (f≫g) j = indexMap P L hL g (indexMap P L hL f j) := by
  change (index P W) ((trackMap P (f≫g)) ((index P U).symm j)) =
    (index P W) ((trackMap P g) ((index P V).symm
      ((index P V) ((trackMap P f) ((index P U).symm j)))))
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def pointMap {U V : Obj P (s:=s)} (f : U ⟶ V) :
    (object P L hL U).polygon.Point ≃ (object P L hL V).polygon.Point where
  toFun x := ⟨(indexMap P L hL f x.val.1,x.val.2), by
    change P.color x.val.2 = ((index P V).symm (indexMap P L hL f x.val.1)).1.1
    rw [indexMap_atom]
    exact x.property⟩
  invFun x := ⟨((indexMap P L hL f).symm x.val.1,x.val.2),by
    have h := indexMap_atom P L hL f ((indexMap P L hL f).symm x.val.1)
    rw [Equiv.apply_symm_apply] at h
    change P.color x.val.2 = ((index P U).symm ((indexMap P L hL f).symm x.val.1)).1.1
    rw [←h]
    exact x.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

noncomputable def arrow {U V : Obj P (s:=s)} (f : U ⟶ V) : object P L hL U ⟶ object P L hL V where
  arrow := relabelArrow (pointMap P L hL f) (indexMap P L hL f) (fun _ => rfl)
  positional _ := rfl
  labelled x := by
    change L (((index P V).symm (indexMap P L hL f x.val.1)).1.2) = _
    rw [indexMap_atom]
    rfl

@[simp] theorem arrow_apply {U V : Obj P (s:=s)} (f : U ⟶ V)
    (x : (object P L hL U).polygon.Point) :
    ((arrow P L hL f).arrow.toEquiv x).val = (indexMap P L hL f x.val.1,x.val.2) := rfl

noncomputable def functor : Obj P (s:=s) ⥤ Labelled a n where
  obj := object P L hL
  map := arrow P L hL
  map_id U := by
    apply Labelled.Hom.ext
    apply Arrow.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [arrow_apply]
    change (indexMap P L hL (𝟙 U) x.val.1,x.val.2) = x.val
    rw [indexMap_id]
  map_comp f g := by
    apply Labelled.Hom.ext
    apply Arrow.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change _ = ((arrow P L hL g).arrow.toEquiv ((arrow P L hL f).arrow.toEquiv x)).val
    rw [arrow_apply,arrow_apply,arrow_apply,indexMap_comp]

instance : (functor P L hL).Faithful where
  map_injective {U V} f g h := by
    funext b
    apply Equiv.ext
    intro k
    let j := index P U ⟨b,k⟩
    let x : (object P L hL U).polygon.Point :=
      ⟨(j,P.point b.1),by simp [object,j,BooleanPartition.cell]⟩
    have hx := congrArg (fun f : object P L hL U ⟶ object P L hL V =>
      (f.arrow.toEquiv x).val.1) h
    change indexMap P L hL f j = indexMap P L hL g j at hx
    have hh := (index P V).injective hx
    change trackMap P f ((index P U).symm j) = trackMap P g ((index P U).symm j) at hh
    simp only [j,Equiv.symm_apply_apply] at hh
    exact Sigma.mk.inj_iff.mp hh |>.2 |> eq_of_heq

end LabelledStage
end SimpleAmenable.PolygonObject

end

section

open CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace LabelledStage
variable {a n s : ℕ} (P : BooleanPartition a)
    (L : Fin s → Fin n → CutRing × CutRing)

structure UniformObject where
  obj : Labelled a n
  uniform : Labelled.ObjectUniform P obj
  supported : ∀ j,∃ l,L l=obj.label j

namespace UniformObject
variable {P L}
structure Hom (U V : UniformObject P L) where
  arrow : U.obj ⟶ V.obj
  uniform : Labelled.ArrowUniform P arrow
@[ext] theorem Hom.ext {U V : UniformObject P L} (f g : Hom U V) (h : f.arrow=g.arrow) : f=g := by
  cases f; cases g; cases h; rfl
noncomputable instance : Category (UniformObject P L) where
  Hom := Hom
  id U := ⟨𝟙 _,Labelled.arrowUniform_id P U.obj⟩
  comp f g := ⟨f.arrow≫g.arrow,Labelled.arrowUniform_comp P f.uniform g.uniform⟩
  id_comp _ := Hom.ext _ _ (Category.id_comp _)
  comp_id _ := Hom.ext _ _ (Category.comp_id _)
  assoc _ _ _ := Hom.ext _ _ (Category.assoc _ _ _)
noncomputable instance {U V : UniformObject P L} (f : U ⟶ V) : IsIso f := by
  refine ⟨⟨⟨inv f.arrow,Labelled.arrowUniform_inv P U.uniform f.uniform⟩,?_,?_⟩⟩
  · exact Hom.ext _ _ (IsIso.hom_inv_id _)
  · exact Hom.ext _ _ (IsIso.inv_hom_id _)
noncomputable instance : Groupoid (UniformObject P L) := Groupoid.ofIsIso (fun _ => inferInstance)

noncomputable def forget : UniformObject P L ⥤ Labelled a n where
  obj U := U.obj
  map f := f.arrow
instance : (forget (P:=P) (L:=L)).Faithful where
  map_injective h := Hom.ext _ _ h

abbrev Fiber (U : UniformObject P L) (b : Fin P.size × Fin s) :=
  {x : U.obj.polygon.Point // x.val.2=P.point b.1 ∧ U.obj.label x.val.1=L b.2}

noncomputable instance (U : UniformObject P L) (b : Fin P.size × Fin s) : Fintype (Fiber U b) :=
  Fintype.ofInjective (fun x : Fiber U b => x.val.val.1) (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext h (x.property.1.trans y.property.1.symm))

noncomputable def fiberMap {U V : UniformObject P L} (f : U ⟶ V) (b : Fin P.size × Fin s) :
    Fiber U b ≃ Fiber V b where
  toFun x := ⟨f.arrow.arrow.toEquiv x.val,
    (f.arrow.positional x.val).trans x.property.1,
    (f.arrow.labelled x.val).trans x.property.2⟩
  invFun y := ⟨f.arrow.arrow.toEquiv.symm y.val,by
    have h := f.arrow.positional (f.arrow.arrow.toEquiv.symm y.val)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans y.property.1,by
    have h := f.arrow.labelled (f.arrow.arrow.toEquiv.symm y.val)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans y.property.2⟩
  left_inv _ := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (Equiv.apply_symm_apply _ _)

noncomputable def evaluation : UniformObject P L ⥤ Obj P (s:=s) where
  obj U b := ⟨Fintype.card (Fiber U b)⟩
  map {U V} f b := (Fintype.equivFin (Fiber U b)).symm.trans
    ((fiberMap f b).trans (Fintype.equivFin (Fiber V b)))
  map_id U := by
    funext b
    apply Equiv.ext
    intro j
    change (Fintype.equivFin (Fiber U b)) ((fiberMap (𝟙 U) b)
      ((Fintype.equivFin (Fiber U b)).symm j))=j
    change (Fintype.equivFin (Fiber U b)) ((Fintype.equivFin (Fiber U b)).symm j)=j
    exact Equiv.apply_symm_apply _ _
  map_comp {U V W} f g := by
    funext b
    apply Equiv.ext
    intro j
    change (Fintype.equivFin (Fiber W b)) ((fiberMap (f≫g) b) _)=
      (Fintype.equivFin (Fiber W b)) ((fiberMap g b)
        ((Fintype.equivFin (Fiber V b)).symm ((Fintype.equivFin (Fiber V b)) _)))
    rw [Equiv.symm_apply_apply]
    rfl

instance : (evaluation (P:=P) (L:=L)).Faithful where
  map_injective {U V} f g h := by
    apply Hom.ext
    apply Labelled.Hom.ext
    apply Arrow.ext
    apply Equiv.ext
    intro x
    obtain ⟨l,hl⟩ := U.supported x.val.1
    let b := (P.color x.val.2,l)
    have hm : P.point b.1∈(U.obj.polygon.cell x.val.1).val :=
      (U.uniform x.val.1 x.val.2 (P.point b.1) (by simp [b])).mp x.property
    let y : Fiber U b := ⟨⟨(x.val.1,P.point b.1),hm⟩,rfl,hl.symm⟩
    have hh := congrFun h b
    have hy := congrArg (fun e : Fin (Fintype.card (Fiber U b)) ≃
        Fin (Fintype.card (Fiber V b)) => e (Fintype.equivFin (Fiber U b) y)) hh
    change (Fintype.equivFin (Fiber V b)) ((fiberMap f b)
        ((Fintype.equivFin (Fiber U b)).symm ((Fintype.equivFin (Fiber U b)) y)))=
      (Fintype.equivFin (Fiber V b)) ((fiberMap g b)
        ((Fintype.equivFin (Fiber U b)).symm ((Fintype.equivFin (Fiber U b)) y))) at hy
    simp only [Equiv.symm_apply_apply] at hy
    have he := (Fintype.equivFin (Fiber V b)).injective hy
    apply Subtype.ext
    apply Prod.ext
    · exact (f.uniform x y.val rfl (by simp [y,b])).trans
        ((congrArg (fun z : Fiber V b => z.val.val.1) he).trans
          (g.uniform x y.val rfl (by simp [y,b])).symm)
    · exact (f.arrow.positional x).trans (g.arrow.positional x).symm

end UniformObject
end LabelledStage
end SimpleAmenable.PolygonObject

end

end

end OAI
