import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk
import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveNormalizationModel PiExponent.CurveModelPlaces
open PiExponent.CurveValuationCenter PiExponent.CurvePlaceCenter
open PiExponent.LocalSectionOrder

namespace PiExponent.CurvePlaceSectionOrder


variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem divisor_eq_local_order (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0)
    (p : NormalizedPlace ℂ E)
    (e : (Scheme.Modules.pullback (centerMorphism f hf p)).obj L.sheaf ≅
      O (Spec (CommRingCat.of (PlaceValuationRing.ring p)))) :
    CurvePlaceSectionDivisor.divisor f hf L s hs p =
      (sectionOrder e (pullbackSection (centerMorphism f hf p) s)).toNat := by
  let : IsDiscreteValuationRing ((parameterCurve f hf).presheaf.stalk
      ((centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)))) := by
    rw [centerMorphism_closedPoint]
    exact parameterCurve_stalkDVR f hf _ (placePoint_ne_genericPoint f hf p)
  have h := LocalPullbackSectionOrder.sectionOrder_eq_germ_order
    (centerMorphism f hf p) L s e
  have hp : (centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≠
      genericPoint (parameterCurve f hf) := by
    rw [centerMorphism_closedPoint]
    exact placePoint_ne_genericPoint f hf p
  have h' : (sectionOrder e (pullbackSection (centerMorphism f hf p) s)).toNat =
      SectionOrderDivisor.orderAt (parameterCurve_stalkDVR f hf) L s
        ⟨(centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)), hp⟩ :=
    congrArg ENat.toNat h
  have heq : (⟨(centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)), hp⟩ :
      SectionOrderDivisor.CurvePoint (parameterCurve f hf)) =
        ⟨placePoint f hf p, placePoint_ne_genericPoint f hf p⟩ := by
    apply Subtype.ext
    exact centerMorphism_closedPoint f hf p
  rw [heq] at h'
  exact (CurvePlaceSectionDivisor.divisor_apply f hf L s hs p).trans h'.symm

end PiExponent.CurvePlaceSectionOrder

end

end OAI
