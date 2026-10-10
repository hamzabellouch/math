import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
universe u

def functionFieldRestriction {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
    (i : U ⟶ X) [IsOpenImmersion i] : X.functionField ⟶ U.functionField :=
  eqToHom (congrArg (fun x => X.presheaf.stalk x)
    (genericPoint_eq_of_isOpenImmersion i).symm) ≫ i.stalkMap (genericPoint U)

private theorem stalkSpecializes_eqToHom (X : Scheme.{u}) {x y : X} (h : x = y) :
    X.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes =
      eqToHom (congrArg (fun z => X.presheaf.stalk z) h.symm) := by
  subst y
  simp

theorem functionFieldRestriction_stalk {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
    (i : U ⟶ X) [IsOpenImmersion i] (q : U) :
    X.presheaf.stalkSpecializes (genericPoint_specializes (i q)) ≫ functionFieldRestriction i =
      i.stalkMap q ≫ U.presheaf.stalkSpecializes (genericPoint_specializes q) := by
  unfold functionFieldRestriction
  rw [← Category.assoc, ← stalkSpecializes_eqToHom X (genericPoint_eq_of_isOpenImmersion i),
    TopCat.Presheaf.stalkSpecializes_comp]
  exact i.stalkSpecializes_stalkMap (genericPoint U) q (genericPoint_specializes q)

private theorem stalkMap_eqToHom {U X : Scheme.{u}} (i : U ⟶ X)
    (x y : U) (h : x = y) :
    i.stalkMap x ≫ eqToHom (congrArg (fun z => U.presheaf.stalk z) h) =
      eqToHom (congrArg (fun z => X.presheaf.stalk (i z)) h) ≫ i.stalkMap y := by
  subst y
  simp

theorem functionFieldRestriction_comp {V U X : Scheme.{u}}
    [IsIntegral V] [IsIntegral U] [IsIntegral X]
    (j : V ⟶ U) (i : U ⟶ X) [IsOpenImmersion j] [IsOpenImmersion i] :
    functionFieldRestriction (j ≫ i) = functionFieldRestriction i ≫ functionFieldRestriction j := by
  symm
  unfold functionFieldRestriction
  rw [Scheme.Hom.stalkMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (i.stalkMap (genericPoint U)),
    stalkMap_eqToHom i (genericPoint U) (j (genericPoint V))
      (genericPoint_eq_of_isOpenImmersion j).symm]
  simp

private theorem toStalk_eqToHom (A : CommRingCat.{u})
    (x y : PrimeSpectrum A) (h : x = y) :
    StructureSheaf.toStalk A x ≫ eqToHom (congrArg
      (fun z => (Spec A).presheaf.stalk z) h) = StructureSheaf.toStalk A y := by
  subst y
  exact Category.comp_id _


theorem functionFieldRestriction_toStalk {A B : CommRingCat.{u}} [IsDomain A] [IsDomain B]
    (f : A ⟶ B) [IsOpenImmersion (Spec.map f)] :
    StructureSheaf.toStalk A (genericPoint (Spec A)) ≫
      functionFieldRestriction (Spec.map f) =
      f ≫ StructureSheaf.toStalk B (genericPoint (Spec B)) := by
  unfold functionFieldRestriction
  erw [← Category.assoc, toStalk_eqToHom A _ _
    (genericPoint_eq_of_isOpenImmersion (Spec.map f)).symm]
  exact AlgebraicGeometry.stalkMap_toStalk f _

end PiExponent.CurveNormalizationModel

end

end OAI
