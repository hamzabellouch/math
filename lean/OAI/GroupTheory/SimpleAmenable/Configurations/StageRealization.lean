import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrajectoryStages

namespace OAI

section

section

open CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace LabelledStage
variable {a n s : ℕ} (P : BooleanPartition a)
    (L : Fin s → Fin n → CutRing × CutRing)
    (hL : ∀ j i, orbitRepresentative (L j i)=L j i)

noncomputable def realizeObject (U : Obj P (s:=s)) : UniformObject P L where
  obj := object P L hL U
  uniform j x y h := by
    change (P.color x=_) ↔ (P.color y=_)
    rw [h]
  supported j := ⟨_,rfl⟩

noncomputable def realize : Obj P (s:=s) ⥤ UniformObject P L where
  obj := realizeObject P L hL
  map f := ⟨arrow P L hL f,fun _ _ h _ => congrArg (indexMap P L hL f) h⟩
  map_id U := UniformObject.Hom.ext _ _ ((functor P L hL).map_id U)
  map_comp f g := UniformObject.Hom.ext _ _ ((functor P L hL).map_comp f g)

namespace UniformObject
variable {P L}
noncomputable def labelIndex (U : UniformObject P L) (j : Fin U.obj.polygon.tracks) : Fin s :=
  (U.supported j).choose
lemma labelIndex_spec (U : UniformObject P L) (j : Fin U.obj.polygon.tracks) :
    L (labelIndex U j)=U.obj.label j := (U.supported j).choose_spec

variable (hLi : Function.Injective L)
include hLi in
lemma labelIndex_fiber (U : UniformObject P L) {b : Fin P.size × Fin s} (y : Fiber U b) :
    labelIndex U y.val.val.1=b.2 := hLi ((labelIndex_spec U _).trans y.property.2)

noncomputable abbrev evaluated (U : UniformObject P L) := (evaluation (P:=P) (L:=L)).obj U

noncomputable def fiberIndex (U : UniformObject P L) :
    Fin (Fintype.card (Track P (evaluated U))) ≃ Σ b : Fin P.size × Fin s,Fiber U b :=
  (index P (evaluated U)).symm.trans
    (Equiv.sigmaCongrRight (fun b => (Fintype.equivFin (Fiber U b)).symm))

noncomputable abbrev trackFiber (U : UniformObject P L)
    (j : Fin (Fintype.card (Track P (evaluated U)))) := (fiberIndex U j).2

noncomputable def sourceAtom (U : UniformObject P L) (x : U.obj.polygon.Point) : Fin P.size × Fin s :=
  (P.color x.val.2,labelIndex U x.val.1)

noncomputable def sample (U : UniformObject P L) (x : U.obj.polygon.Point) : Fiber U (sourceAtom U x) :=
  ⟨⟨(x.val.1,P.point (P.color x.val.2)),
    (U.uniform x.val.1 x.val.2 (P.point (P.color x.val.2)) (by simp)).mp x.property⟩,
    rfl,(labelIndex_spec U _).symm⟩

noncomputable def sourceIndex (U : UniformObject P L) (x : U.obj.polygon.Point) :
    Fin (Fintype.card (Track P (evaluated U))) :=
  (fiberIndex U).symm ⟨sourceAtom U x,sample U x⟩

@[simp] lemma sourceIndex_atom (U : UniformObject P L) (x : U.obj.polygon.Point) :
    ((index P (evaluated U)).symm (sourceIndex U x)).1=sourceAtom U x := by
  change (fiberIndex U ((fiberIndex U).symm ⟨sourceAtom U x,sample U x⟩)).1=_
  rw [Equiv.apply_symm_apply]

@[simp] lemma sourceIndex_track (U : UniformObject P L) (x : U.obj.polygon.Point) :
    (trackFiber U (sourceIndex U x)).val.val.1=x.val.1 := by
  change (fiberIndex U ((fiberIndex U).symm ⟨sourceAtom U x,sample U x⟩)).2.val.val.1=_
  rw [Equiv.apply_symm_apply]
  rfl

variable (P L)
noncomputable def reconstructMap (U : UniformObject P L)
    (x : (object P L hL (evaluated U)).polygon.Point) : U.obj.polygon.Point :=
  ⟨((trackFiber U x.val.1).val.val.1,x.val.2),by
    have h := (trackFiber U x.val.1).val.property
    have hc : P.color (trackFiber U x.val.1).val.val.2=P.color x.val.2 := by
      rw [(trackFiber U x.val.1).property.1,BooleanPartition.color_point]
      exact x.property.symm
    exact (U.uniform _ _ _ hc).mp h⟩

noncomputable def reconstructInverse (U : UniformObject P L) (x : U.obj.polygon.Point) :
    (object P L hL (evaluated U)).polygon.Point :=
  ⟨(sourceIndex U x,x.val.2),by
    change P.color x.val.2=((index P (evaluated U)).symm (sourceIndex U x)).1.1
    rw [sourceIndex_atom]
    rfl⟩

lemma reconstruct_right (U : UniformObject P L) (x : U.obj.polygon.Point) :
    reconstructMap P L hL U (reconstructInverse P L hL U x)=x := by
  apply Subtype.ext
  apply Prod.ext
  · exact sourceIndex_track U x
  · rfl

include hLi in
lemma reconstruct_left (U : UniformObject P L)
    (x : (object P L hL (evaluated U)).polygon.Point) :
    reconstructInverse P L hL U (reconstructMap P L hL U x)=x := by
  apply Subtype.ext
  apply Prod.ext
  · change sourceIndex U (reconstructMap P L hL U x)=x.val.1
    apply (fiberIndex U).injective
    change fiberIndex U ((fiberIndex U).symm _) = _
    rw [Equiv.apply_symm_apply]
    have hb : sourceAtom U (reconstructMap P L hL U x)=(fiberIndex U x.val.1).1 := by
      apply Prod.ext
      · exact x.property
      · exact labelIndex_fiber hLi U (trackFiber U x.val.1)
    apply Sigma.ext hb
    apply (Subtype.heq_iff_coe_eq (by intro y; dsimp only; rw [hb])).mpr
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change P.point (P.color x.val.2)=(trackFiber U x.val.1).val.val.2
      rw [show P.color x.val.2=(fiberIndex U x.val.1).1.1 from x.property]
      exact (trackFiber U x.val.1).property.1.symm

  · rfl

noncomputable def reconstructEquiv (U : UniformObject P L) :
    (object P L hL (evaluated U)).polygon.Point ≃ U.obj.polygon.Point where
  toFun := reconstructMap P L hL U
  invFun := reconstructInverse P L hL U
  left_inv := reconstruct_left P L hL hLi U
  right_inv := reconstruct_right P L hL U

end UniformObject
end LabelledStage
end SimpleAmenable.PolygonObject

end

section

open CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace LabelledStage
variable {a n s : ℕ} (P : BooleanPartition a)
    (L : Fin s → Fin n → CutRing × CutRing)
    (hL : ∀ j i, orbitRepresentative (L j i)=L j i)
    (hLi : Function.Injective L)

namespace UniformObject
noncomputable def reconstruct (U : UniformObject P L) :
    (realize P L hL).obj (evaluated U) ⟶ U where
  arrow := {
    arrow := relabelArrow (reconstructEquiv P L hL hLi U)
      (fun j => (trackFiber U j).val.val.1) (fun _ => rfl)
    positional := fun _ => rfl
    labelled := fun x => (trackFiber U x.val.1).property.2 }
  uniform := fun _ _ h _ => congrArg (fun j => (trackFiber U j).val.val.1) h
end UniformObject

open UniformObject
include hLi in
theorem realize_essSurj : (realize P L hL).EssSurj := {
  mem_essImage U := ⟨evaluated U,⟨asIso (reconstruct P L hL hLi U)⟩⟩ }

instance realize_faithful : (realize P L hL).Faithful where
  map_injective equality := (functor P L hL).map_injective (congrArg Hom.arrow equality)

noncomputable def fiberPoint (U : Obj P (s:=s)) (b : Fin P.size × Fin s) (k : Fin (U b).size) :
    Fiber (realizeObject P L hL U) b :=
  ⟨⟨(index P U ⟨b,k⟩,P.point b.1),by
    change P.color (P.point b.1)=((index P U).symm ((index P U) ⟨b,k⟩)).1.1
    rw [Equiv.symm_apply_apply,BooleanPartition.color_point]⟩,rfl,by
    change L (((index P U).symm ((index P U) ⟨b,k⟩)).1.2)=L b.2
    rw [Equiv.symm_apply_apply]⟩

include hLi in
lemma fiber_base (U : Obj P (s:=s)) (b : Fin P.size × Fin s)
    (y : Fiber (realizeObject P L hL U) b) :
    ((index P U).symm y.val.val.1).1=b := by
  apply Prod.ext
  · have hp := y.val.property
    change P.color y.val.val.2=((index P U).symm y.val.val.1).1.1 at hp
    rw [y.property.1,BooleanPartition.color_point] at hp
    exact hp.symm
  · apply hLi
    exact y.property.2

noncomputable def fiberFin (U : Obj P (s:=s)) (b : Fin P.size × Fin s)
    (y : Fiber (realizeObject P L hL U) b) : Fin (U b).size :=
  (fiber_base P L hL hLi U b y) ▸ ((index P U).symm y.val.val.1).2

lemma fiberFin_spec (U : Obj P (s:=s)) (b : Fin P.size × Fin s)
    (y : Fiber (realizeObject P L hL U) b) :
    (⟨b,fiberFin P L hL hLi U b y⟩ : Track P U)=((index P U).symm y.val.val.1) := by
  apply Sigma.ext (fiber_base P L hL hLi U b y).symm
  dsimp only [fiberFin]
  exact eqRec_heq (φ:=fun b => Fin (U b).size) _ _

noncomputable def fiberEquiv (U : Obj P (s:=s)) (b : Fin P.size × Fin s) :
    Fin (U b).size ≃ Fiber (realizeObject P L hL U) b where
  toFun := fiberPoint P L hL U b
  invFun := fiberFin P L hL hLi U b
  left_inv k := by
    have h := fiberFin_spec P L hL hLi U b (fiberPoint P L hL U b k)
    change (⟨b,_⟩ : Track P U)=(index P U).symm ((index P U) ⟨b,k⟩) at h
    rw [Equiv.symm_apply_apply] at h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change index P U ⟨b,fiberFin P L hL hLi U b y⟩=y.val.val.1
      rw [fiberFin_spec]
      exact Equiv.apply_symm_apply (index P U) y.val.val.1
    · exact y.property.1.symm

noncomputable def fromUniform {U V : Obj P (s:=s)}
    (f : (realize P L hL).obj U ⟶ (realize P L hL).obj V) : ∀b,Fin (U b).size ≃ Fin (V b).size :=
  fun b => (fiberEquiv P L hL hLi U b).trans
    ((fiberMap f b).trans (fiberEquiv P L hL hLi V b).symm)

lemma fromUniform_spec {U V : Obj P (s:=s)}
    (f : (realize P L hL).obj U ⟶ (realize P L hL).obj V)
    (b : Fin P.size × Fin s) (k : Fin (U b).size) :
    index P V ⟨b,fromUniform P L hL hLi f b k⟩ =
      (f.arrow.arrow.toEquiv (fiberPoint P L hL U b k).val).val.1 := by
  change (index P V) ⟨b,fiberFin P L hL hLi V b ((fiberMap f b) (fiberPoint P L hL U b k))⟩=_
  exact (congrArg (index P V)
    (fiberFin_spec P L hL hLi V b ((fiberMap f b) (fiberPoint P L hL U b k)))).trans
      ((index P V).apply_symm_apply _)

include hLi in
theorem realize_full : (realize P L hL).Full := {
  map_surjective {U V} f := ⟨fromUniform P L hL hLi f,by
    apply Hom.ext
    apply Labelled.Hom.ext
    apply Arrow.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · change indexMap P L hL (fromUniform P L hL hLi f) x.val.1=(f.arrow.arrow.toEquiv x).val.1
      let t := (index P U).symm x.val.1
      have h := fromUniform_spec P L hL hLi f t.1 t.2
      change (index P V) ⟨t.1,fromUniform P L hL hLi f t.1 t.2⟩=(f.arrow.arrow.toEquiv x).val.1
      rw [h]
      apply f.uniform
      · change (index P U) ((index P U).symm x.val.1)=x.val.1
        exact Equiv.apply_symm_apply _ _
      · change P.color (P.point t.1.1)=P.color x.val.2
        rw [BooleanPartition.color_point]
        exact x.property.symm
    · exact (f.arrow.positional x).symm⟩ }

noncomputable def equivalence : Obj P (s:=s) ≌ UniformObject P L := by
  letI := (inferInstance : (realize P L hL).Faithful)
  letI := (realize_full P L hL hLi)
  letI := (realize_essSurj P L hL hLi)
  letI : (realize P L hL).IsEquivalence := {}
  exact (realize P L hL).asEquivalence

end LabelledStage
end SimpleAmenable.PolygonObject

end

end

end OAI
