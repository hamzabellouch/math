import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PairLawAssembly
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonGroupoid

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonObjectRefinement

open Classical CategoryTheory Set
namespace PolygonObject
variable {a : ℕ}

noncomputable def shifted (U : PolygonObject a) (d : Fin U.tracks → CutRing × CutRing) :
    PolygonObject a := ⟨U.tracks,fun i => ⟨translation a (d i) '' (U.cell i).val,
      polygon_image_translation _ (U.cell i).property⟩⟩

noncomputable def shiftEquiv (U : PolygonObject a) (d : Fin U.tracks → CutRing × CutRing) :
    U.Point ≃ (shifted U d).Point where
  toFun x := ⟨(x.val.1,translate a (d x.val.1) x.val.2),⟨x.val.2,x.property,rfl⟩⟩
  invFun y := ⟨(y.val.1,translate a (-d y.val.1) y.val.2),by
    obtain ⟨x,hx,he⟩ := y.property
    change translate a (-d y.val.1) y.val.2∈(U.cell y.val.1).val
    rw [←he]
    simpa only [translation_apply,←translate_add,neg_add_cancel,translate_zero] using hx⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (by
      change translate a (-d x.val.1) (translate a (d x.val.1) x.val.2)=x.val.2
      rw [←translate_add,neg_add_cancel,translate_zero])
  right_inv y := by
    apply Subtype.ext
    exact Prod.ext rfl (by
      change translate a (d y.val.1) (translate a (-d y.val.1) y.val.2)=y.val.2
      rw [←translate_add,add_neg_cancel,translate_zero])

noncomputable def shiftArrow (U : PolygonObject a) (d : Fin U.tracks → CutRing × CutRing) :
    U ⟶ shifted U d where
  toEquiv := shiftEquiv U d
  hasTable := by
    let c : Fin U.tracks → Chart (a:=a) U.tracks U.tracks := fun i => ⟨i,i,d i,U.cell i⟩
    refine ⟨Finset.univ.image c,?_,?_⟩
    · intro k hk
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
      intro x hx
      exact ⟨hx,rfl⟩
    · intro x
      exact ⟨c x.val.1,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,rfl,x.property⟩

@[simp] theorem shiftArrow_apply (U : PolygonObject a) (d : Fin U.tracks → CutRing × CutRing)
    (x : U.Point) : (shiftArrow U d).toEquiv x=
      ⟨(x.val.1,translate a (d x.val.1) x.val.2),⟨x.val.2,x.property,rfl⟩⟩ := rfl

variable {κ : Type} [Fintype κ]

noncomputable def refinement (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a) :
    PolygonObject a :=
  ⟨Fintype.card (Fin U.tracks × κ),fun j =>
    let ik := (Fintype.equivFin (Fin U.tracks × κ)).symm j
    ⟨{z | ∃hz : z∈(U.cell ik.1).val,label ⟨(ik.1,z),hz⟩=ik.2},hpoly ik.1 ik.2⟩⟩

noncomputable def refinementEquiv (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a) :
    (refinement U label hpoly).Point ≃ U.Point where
  toFun x :=
    ⟨(((Fintype.equivFin (Fin U.tracks × κ)).symm x.val.1).1,x.val.2),x.property.choose⟩
  invFun y := ⟨((Fintype.equivFin _) (y.val.1,label y),y.val.2),by
    change ∃hz : _∈(U.cell _).val,label ⟨(_,y.val.2),hz⟩=_
    simp only [Equiv.symm_apply_apply]
    exact ⟨y.property,True.intro⟩⟩
  left_inv x := by
    apply Subtype.ext
    change ((Fintype.equivFin (Fin U.tracks × κ))
      (((Fintype.equivFin (Fin U.tracks × κ)).symm x.val.1).1,
        label ⟨(((Fintype.equivFin (Fin U.tracks × κ)).symm x.val.1).1,x.val.2),x.property.choose⟩),x.val.2)=
      (x.val.1,x.val.2)
    apply Prod.ext
    · apply (Fintype.equivFin (Fin U.tracks × κ)).symm.injective
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext rfl x.property.choose_spec
    · rfl
  right_inv y := by
    apply Subtype.ext
    exact Prod.ext (by simp) rfl

noncomputable def refinementArrow (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a) :
    refinement U label hpoly ⟶ U where
  toEquiv := refinementEquiv U label hpoly
  hasTable := by
    let V := refinement U label hpoly
    let c : Fin V.tracks → Chart (a:=a) V.tracks U.tracks := fun j =>
      ⟨j,((Fintype.equivFin (Fin U.tracks × κ)).symm j).1,0,V.cell j⟩
    refine ⟨Finset.univ.image c,?_,?_⟩
    · intro k hk
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hk
      intro x hx
      refine ⟨hx,?_⟩
      change (((Fintype.equivFin (Fin U.tracks × κ)).symm j).1,x)=
        (((Fintype.equivFin (Fin U.tracks × κ)).symm j).1,translate a 0 x)
      rw [translate_zero]
    · intro x
      exact ⟨c x.val.1,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,rfl,x.property⟩

theorem refinementArrow_positional (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a) :
    Positional (refinementArrow U label hpoly) := fun _ => rfl

theorem refinementArrow_label (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a)
    (x : (refinement U label hpoly).Point) :
    label ((refinementArrow U label hpoly).toEquiv x)=
      ((Fintype.equivFin (Fin U.tracks × κ)).symm x.val.1).2 := x.property.choose_spec

end PolygonObject
end PolygonObjectRefinement

end SimpleAmenable
end
end

end OAI
