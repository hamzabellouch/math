import Mathlib.AlgebraicGeometry.Stalk
import OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
open scoped Polynomial
open PiExponent.CurveZeroPole
universe u

private theorem eqToHom_fromSpecStalk (X : Scheme.{u}) {x y : X} (h : x = y) :
    Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) h)) ≫
      X.fromSpecStalk x = X.fromSpecStalk y := by
  subst y
  simp

theorem functionFieldRestriction_fromSpecStalk {U X : Scheme.{u}}
    [IsIntegral U] [IsIntegral X] (i : U ⟶ X) [IsOpenImmersion i] :
    Spec.map (functionFieldRestriction i) ≫ X.fromSpecStalk (genericPoint X) =
      U.fromSpecStalk (genericPoint U) ≫ i := by
  unfold functionFieldRestriction
  rw [Spec.map_comp, Category.assoc,
    eqToHom_fromSpecStalk X (genericPoint_eq_of_isOpenImmersion i).symm]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk i


theorem affineFunctionFieldEquiv_fromSpecStalk
    (A E : Type u) [CommRing A] [IsDomain A] [Field E]
    [Algebra A E] [IsFractionRing A E] :
    Spec.map (CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom) ≫
      (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) := by
  erw [Spec.fromSpecStalk_eq', ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact affineFunctionFieldEquiv_toStalk A E

private theorem affineRestriction_fromSpecStalk
    (A E : Type u) [CommRing A] [IsDomain A] [Field E]
    [Algebra A E] [IsFractionRing A E] {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] :
    Spec.map (functionFieldRestriction i ≫
      CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom) ≫
      X.fromSpecStalk (genericPoint X) =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ i := by
  let e := Spec.map (CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom)
  let r := Spec.map (functionFieldRestriction i)
  let q := X.fromSpecStalk (genericPoint X)
  have hmap := congrArg (fun k => k ≫ q)
    (Spec.map_comp (functionFieldRestriction i)
      (CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom))
  have hrestrict := congrArg (fun k => e ≫ k) (functionFieldRestriction_fromSpecStalk i)
  have haffine := congrArg (fun k => k ≫ i) (affineFunctionFieldEquiv_fromSpecStalk A E)
  have hassoc := Category.assoc e
    ((Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))) i
  exact hmap.trans ((Category.assoc e r q).trans
    (hrestrict.trans (hassoc.symm.trans haffine)))

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterChartConstantMap : F →+* parameterChart f hf :=
  letI := parameterPolynomialAlgebra f hf
  (algebraMap F[X] (parameterChart f hf)).comp Polynomial.C

theorem parameterChartConstantMap_toField :
    (algebraMap (parameterChart f hf) E).comp (parameterChartConstantMap f hf) =
      algebraMap F E := by
  let := parameterPolynomialAlgebra f hf
  apply RingHom.ext
  intro c
  change algebraMap F[X] E (Polynomial.C c) = algebraMap F E c
  rw [parameterPolynomialAlgebra_map]
  simp

@[reassoc] theorem zeroChart_structureMap :
    zeroChartInclusion f hf ≫ parameterCurveStructureMap f hf =
      Spec.map (CommRingCat.ofHom (parameterChartConstantMap f hf)) := by
  unfold parameterCurveStructureMap
  rw [zeroChart_projection_assoc, ProjectiveLine.chartMap_structureMap,
    parameterChartProjection, ← Spec.map_comp]
  rfl

variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]

def parameterCurveGenericPoint : Spec (.of E) ⟶ parameterCurve f hf :=
  Spec.map (CommRingCat.ofHom (parameterCurveFunctionFieldEquiv f hf).toRingHom) ≫
    (parameterCurve f hf).fromSpecStalk (genericPoint (parameterCurve f hf))

theorem parameterCurveGenericPoint_eq_zeroChart :
    parameterCurveGenericPoint f hf =
      Spec.map (CommRingCat.ofHom (algebraMap (parameterChart f hf) E)) ≫
        zeroChartInclusion f hf := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change Spec.map (functionFieldRestriction (zeroChartInclusion f hf) ≫
      CommRingCat.ofHom (affineFunctionFieldEquiv (parameterChart f hf) E).toRingHom) ≫
      (parameterCurve f hf).fromSpecStalk (genericPoint (parameterCurve f hf)) = _
  exact affineRestriction_fromSpecStalk (parameterChart f hf) E (zeroChartInclusion f hf)

@[reassoc] theorem parameterCurveGenericPoint_over_base :
    parameterCurveGenericPoint f hf ≫ parameterCurveStructureMap f hf =
      Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
  rw [parameterCurveGenericPoint_eq_zeroChart, Category.assoc,
    zeroChart_structureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact parameterChartConstantMap_toField f hf

end PiExponent.CurveNormalizationModel

end

end OAI
