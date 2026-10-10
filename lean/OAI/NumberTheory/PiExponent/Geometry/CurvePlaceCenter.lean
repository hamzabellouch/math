import OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint
import OAI.NumberTheory.PiExponent.Geometry.CurveModelInfinityGenericPoint
import OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurvePlaceCenter
open AlgebraicGeometry CategoryTheory
open CurveZeroPole CurveValuationCenter CurveNormalizationModel CurveModelPlaces

theorem fractionSpec_isDominant
    (A E : Type u) [CommRing A] [IsDomain A] [Field E] [Algebra A E] [IsFractionRing A E] :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A E))) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure (Spec (CommRingCat.of A))]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  refine ⟨(⊥ : PrimeSpectrum E), ?_⟩
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  ext a
  change algebraMap A E a = 0 ↔ a = 0
  exact map_eq_zero_iff _ (IsFractionRing.injective A E)

theorem hom_ext_fraction
    (A E : Type u) [CommRing A] [IsDomain A] [Field E] [Algebra A E] [IsFractionRing A E]
    {Y : Scheme.{u}} [Y.IsSeparated] (g h : Spec (CommRingCat.of A) ⟶ Y)
    (heq : Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ h) : g = h := by
  let := fractionSpec_isDominant A E
  exact ext_of_isDominant (Spec.map (CommRingCat.ofHom (algebraMap A E))) heq

def centerMorphism
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) :
    Spec (CommRingCat.of (PlaceValuationRing.ring p)) ⟶ parameterCurve f hf :=
  if hp : 0 ≤ p.valuation f then
    Spec.map (CommRingCat.ofHom (parameterChartValuationHom f hf p.valuation p.constants_nonneg hp)) ≫
      zeroChartInclusion f hf
  else
    Spec.map (CommRingCat.ofHom (parameterChartValuationHom f⁻¹ (transcendental_inverse f hf)
      p.valuation p.constants_nonneg (inverse_positive_of_not_regular p f hf.ne_zero hp).le)) ≫
      infinityChartInclusion f hf

theorem centerMorphism_closedPoint
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) :
    centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
      placePoint f hf p := by
  by_cases hp : 0 ≤ p.valuation f
  · simp only [centerMorphism, placePoint, dite_eq_left hp]
    rfl
  · simp only [centerMorphism, placePoint, dite_eq_right hp]
    rfl

theorem centerMorphism_generic_of_regular
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    Spec.map (CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E)) ≫
      centerMorphism f hf p = parameterCurveGenericPoint f hf := by
  rw [centerMorphism, dite_eq_left hp, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, parameterCurveGenericPoint_eq_zeroChart]
  rfl

theorem centerMorphism_generic
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) :
    Spec.map (CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E)) ≫
      centerMorphism f hf p = parameterCurveGenericPoint f hf := by
  by_cases hp : 0 ≤ p.valuation f
  · exact centerMorphism_generic_of_regular f hf p hp
  · rw [centerMorphism, dite_eq_right hp, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, parameterCurveGenericPoint_eq_infinityChart]
    rfl

theorem centerMorphism_over_base
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) :
    centerMorphism f hf p ≫ parameterCurveStructureMap f hf =
      Spec.map (CommRingCat.ofHom (algebraMap F (PlaceValuationRing.ring p))) := by
  apply hom_ext_fraction (PlaceValuationRing.ring p) E
  rw [← Category.assoc, centerMorphism_generic, parameterCurveGenericPoint_over_base,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem centerMorphism_comp_eq_of_generic
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) {Y : Scheme.{u}} [Y.IsSeparated]
    (g : parameterCurve f hf ⟶ Y)
    (φ : Spec (CommRingCat.of (PlaceValuationRing.ring p)) ⟶ Y)
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E)) ≫ φ =
      parameterCurveGenericPoint f hf ≫ g) : centerMorphism f hf p ≫ g = φ := by
  apply hom_ext_fraction (PlaceValuationRing.ring p) E
  rw [← Category.assoc, centerMorphism_generic]
  exact hφ.symm

end PiExponent.CurvePlaceCenter

end

end OAI
