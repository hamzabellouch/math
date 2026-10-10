import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonStringNormalization

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonStrandReconstruction

open Classical CategoryTheory
namespace PolygonObject
variable {a n : ℕ}

theorem representative_sub (u v : CutRing × CutRing) :
    orbitRepresentative (u-v)=orbitRepresentative u-orbitRepresentative v := by
  simp [orbitRepresentative,sub_mul]

theorem trajectoryShift_translationString (U : PolygonObject a)
    (d : Fin (n+1) → Fin U.tracks → CutRing × CutRing) (x : U.Point) (i : Fin (n+1)) :
    trajectoryShift (translationString U d) ((shiftArrow U (d 0)).toEquiv x) i=
      orbitRepresentative (d i x.val.1-d 0 x.val.1) := by
  apply pointShift_unique
  change ((CategoryTheory.inv (shiftArrow U (d 0)) ≫ shiftArrow U (d i)).toEquiv
    ((shiftArrow U (d 0)).toEquiv x)).val.2 = _
  simp only [arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
  simp only [shiftArrow_apply]
  rw [←translate_add,sub_add_cancel]

theorem increments_translationString (U : PolygonObject a)
    (d : Fin (n+1) → Fin U.tracks → CutRing × CutRing) (x : U.Point) (i : Fin n) :
    increments (translationString U d) ((shiftArrow U (d 0)).toEquiv x) i=
      orbitRepresentative (d i.succ x.val.1-d i.castSucc x.val.1) := by
  unfold increments
  rw [trajectoryShift_translationString,trajectoryShift_translationString,←representative_sub]
  congr 1
  abel

noncomputable def incrementString (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing) : RawString a n :=
  translationString U (fun i j => Fin.partialSum (γ j) i)

noncomputable def incrementInitial (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing) : U ⟶ (incrementString U γ).obj 0 :=
  shiftArrow U (fun j => Fin.partialSum (γ j) 0)

theorem incrementInitial_positional (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing) : Positional (incrementInitial U γ) := by
  intro x
  change translate a (Fin.partialSum (γ x.val.1) 0) x.val.2=x.val.2
  rw [Fin.partialSum_zero,translate_zero]

theorem incrementString_spec (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing) (x : U.Point) (i : Fin n) :
    increments (incrementString U γ) ((incrementInitial U γ).toEquiv x) i=
      orbitRepresentative (γ x.val.1 i) := by
  change increments (translationString U (fun i j => Fin.partialSum (γ j) i))
    ((shiftArrow U (fun j => Fin.partialSum (γ j) 0)).toEquiv x) i=_
  rw [increments_translationString,Fin.partialSum_succ]
  congr 1
  abel

theorem incrementString_spec_reduced (U : PolygonObject a)
    (γ : Fin U.tracks → Fin n → CutRing × CutRing)
    (hγ : ∀j i,orbitRepresentative (γ j i)=γ j i) (x : U.Point) :
    increments (incrementString U γ) ((incrementInitial U γ).toEquiv x)=γ x.val.1 := by
  funext i
  rw [incrementString_spec,hγ]

end PolygonObject
end PolygonStrandReconstruction

section PolygonIncrementFibers

open Classical CategoryTheory
namespace PolygonObject
variable {a n : ℕ}

theorem partialSum_increments (F : RawString a n) (x : (F.obj 0).Point) (i : Fin (n+1)) :
    Fin.partialSum (increments F x) i=trajectoryShift F x i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    rw [Fin.partialSum_succ,hi]
    unfold increments
    abel

theorem trajectory_eq_of_increments {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0)
    (hp : Positional h) (he : ∀x,increments G (h.toEquiv x)=increments F x)
    (x : (F.obj 0).Point) : trajectory G (h.toEquiv x)=trajectory F x := by
  funext i
  unfold trajectory
  rw [pointShift_spec (baseArrow G i),pointShift_spec (baseArrow F i)]
  change translate a (trajectoryShift G (h.toEquiv x) i) (h.toEquiv x).val.2=
    translate a (trajectoryShift F x i) x.val.2
  rw [hp x,←partialSum_increments,←partialSum_increments,he x]

theorem extendLadder_positional_of_increments {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0)
    (hp : Positional h) (he : ∀x,increments G (h.toEquiv x)=increments F x) :
    (ladderProperty a n) (extendLadder h) :=
  extendLadder_positional h (trajectory_eq_of_increments h hp he)

noncomputable def incrementLadderEquiv (F G : StringGroupoid a n) :
    (F ⟶ G) ≃ {h : F.obj.obj 0 ⟶ G.obj.obj 0 //
      Positional h ∧ ∀x,increments G.obj (h.toEquiv x)=increments F.obj x} where
  toFun h := ⟨h.hom.app 0,h.property 0,ladder_preserves_increments h⟩
  invFun h := ⟨extendLadder h.val,
    extendLadder_positional_of_increments h.val h.property.1 h.property.2⟩
  left_inv h := by apply WideSubcategory.hom_ext; exact extendLadder_app_zero h.hom
  right_inv h := by apply Subtype.ext; exact extendLadder_zero h.val

end PolygonObject
end PolygonIncrementFibers

end SimpleAmenable
end
end

end OAI
