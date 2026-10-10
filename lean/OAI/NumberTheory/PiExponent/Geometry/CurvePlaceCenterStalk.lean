import OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk
import OAI.NumberTheory.PiExponent.Geometry.CurveModelLocalOrder
import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter

namespace OAI

noncomputable section
namespace PiExponent.CurvePlaceCenter
open CategoryTheory AlgebraicGeometry
open CurveZeroPole CurveValuationCenter CurveNormalizationModel CurveModelPlaces
universe u
variable {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]
variable (p : NormalizedPlace F E)

instance centerMorphism_stalkMap_isIso :
    IsIso ((centerMorphism f hf p).stalkMap (IsLocalRing.closedPoint (PlaceValuationRing.ring p))) := by
  have hx : centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≠
      genericPoint (parameterCurve f hf) := by
    rw [centerMorphism_closedPoint]
    exact placePoint_ne_genericPoint f hf p
  let := parameterCurve_stalkDVR f hf _ hx
  exact BirationalValuationStalk.stalkMap_isIso (centerMorphism f hf p)
    (parameterCurveFunctionFieldEquiv f hf) (centerMorphism_generic f hf p)

instance centerMorphism_stalkClosedPointTo_isIso :
    IsIso (Scheme.stalkClosedPointTo (centerMorphism f hf p)) := by
  unfold Scheme.stalkClosedPointTo
  infer_instance

def centerStalkIso :
    (parameterCurve f hf).presheaf.stalk (placePoint f hf p) ≅
      CommRingCat.of (PlaceValuationRing.ring p) :=
  (parameterCurve f hf).presheaf.stalkCongr
      (.of_eq (centerMorphism_closedPoint f hf p).symm) ≪≫
    asIso (Scheme.stalkClosedPointTo (centerMorphism f hf p))

@[reassoc]
theorem centerStalkIso_hom_eq :
    (centerStalkIso f hf p).hom =
      ((parameterCurve f hf).presheaf.stalkCongr
        (.of_eq (centerMorphism_closedPoint f hf p).symm)).hom ≫
      (centerMorphism f hf p).stalkMap (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≫
      (stalkClosedPointIso (.of (PlaceValuationRing.ring p))).hom := rfl

omit [CharZero F] in
theorem centerMorphism_stalkClosedPointTo_field :
    (algebraMap (PlaceValuationRing.ring p) E).comp
        (Scheme.stalkClosedPointTo (centerMorphism f hf p)).hom =
      (parameterCurveFunctionFieldEquiv f hf).toRingHom.comp
        (algebraMap ((parameterCurve f hf).presheaf.stalk
          (centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p))))
          (parameterCurve f hf).functionField) :=
  BirationalValuationStalk.stalkClosedPointTo_field_compatibility (centerMorphism f hf p)
    (parameterCurveFunctionFieldEquiv f hf) (centerMorphism_generic f hf p)

end PiExponent.CurvePlaceCenter

end

end OAI
