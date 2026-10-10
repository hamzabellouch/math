import Mathlib

namespace OAI

noncomputable section
namespace PiExponent.BirationalValuationStalk
open CategoryTheory AlgebraicGeometry

private theorem comp_eq_of_comp_eq {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ Z) (hcomp : g ≫ h = k) :
    (f ≫ g) ≫ h = f ≫ k :=
  (Category.assoc f g h).trans (congrArg (fun t => f ≫ t) hcomp)

universe u
variable {X : Scheme.{u}} [IsIntegral X]
variable {A E : Type u} [CommRing A] [IsLocalRing A]
  [Field E] [Algebra A E] [IsFractionRing A E]
variable (g : Spec (.of A) ⟶ X) (e : X.functionField ≃+* E)
variable (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ g =
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X))

include hgeneric


omit [IsFractionRing A E] in
theorem stalkClosedPointTo_field_compatibility :
    (algebraMap A E).comp (Scheme.stalkClosedPointTo g).hom =
      e.toRingHom.comp
        (algebraMap (X.presheaf.stalk (g (IsLocalRing.closedPoint A))) X.functionField) := by
  have h : Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom (algebraMap A E) =
      X.presheaf.stalkSpecializes (genericPoint_specializes (g (IsLocalRing.closedPoint A))) ≫
        CommRingCat.ofHom e.toRingHom := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (g (IsLocalRing.closedPoint A)))).mp
    let q := X.fromSpecStalk (g (IsLocalRing.closedPoint A))
    have hleft := comp_eq_of_comp_eq
      (Spec.map (CommRingCat.ofHom (algebraMap A E)))
      (Spec.map (Scheme.stalkClosedPointTo g)) q g
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk g)
    have hright := comp_eq_of_comp_eq
      (Spec.map (CommRingCat.ofHom e.toRingHom))
      (Spec.map (X.presheaf.stalkSpecializes
        (genericPoint_specializes (g (IsLocalRing.closedPoint A))))) q
      (X.fromSpecStalk (genericPoint X))
      (X.SpecMap_stalkSpecializes_fromSpecStalk
        (genericPoint_specializes (g (IsLocalRing.closedPoint A))))
    have hmapLeft := congrArg (fun k => k ≫ q)
      (Spec.map_comp (Scheme.stalkClosedPointTo g) (CommRingCat.ofHom (algebraMap A E)))
    have hmapRight := congrArg (fun k => k ≫ q)
      (Spec.map_comp (X.presheaf.stalkSpecializes
        (genericPoint_specializes (g (IsLocalRing.closedPoint A))))
        (CommRingCat.ofHom e.toRingHom))
    exact hmapLeft.trans (hleft.trans (hgeneric.trans (hright.symm.trans hmapRight.symm)))
  exact CommRingCat.hom_ext_iff.mp h


theorem stalkClosedPointTo_bijective
    [ValuationRing (X.presheaf.stalk (g (IsLocalRing.closedPoint A)))] :
    Function.Bijective (Scheme.stalkClosedPointTo g).hom := by
  let α := (Scheme.stalkClosedPointTo g).hom
  let β := e.symm.toRingHom.comp (algebraMap A E)
  have hcomp : β.comp α =
      algebraMap (X.presheaf.stalk (g (IsLocalRing.closedPoint A))) X.functionField := by
    apply RingHom.ext
    intro a
    apply e.injective
    have h := RingHom.congr_fun (stalkClosedPointTo_field_compatibility g e hgeneric) a
    change e (e.symm ((algebraMap A E) (α a))) =
      e ((algebraMap (X.presheaf.stalk (g (IsLocalRing.closedPoint A))) X.functionField) a)
    rw [e.apply_symm_apply]
    exact h
  have hβ : Function.Injective β := e.symm.injective.comp (IsFractionRing.injective A E)
  have hbij := bijective_rangeRestrict_comp_of_valuationRing α β hcomp
  refine ⟨fun a b hab => hbij.1 (congrArg β.rangeRestrict hab), ?_⟩
  intro a
  obtain ⟨b, hb⟩ := hbij.2 (β.rangeRestrict a)
  refine ⟨b, hβ ?_⟩
  exact congrArg Subtype.val hb

theorem stalkMap_isIso
    [ValuationRing (X.presheaf.stalk (g (IsLocalRing.closedPoint A)))] :
    IsIso (g.stalkMap (IsLocalRing.closedPoint A)) := by
  have : IsIso (Scheme.stalkClosedPointTo g) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (stalkClosedPointTo_bijective g e hgeneric)
  change IsIso (g.stalkMap _ ≫ (stalkClosedPointIso (.of A)).hom) at this
  exact IsIso.of_isIso_comp_right _ (stalkClosedPointIso (.of A)).hom

end PiExponent.BirationalValuationStalk

end

end OAI
