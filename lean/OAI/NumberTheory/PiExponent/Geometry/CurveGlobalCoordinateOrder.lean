import OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal
import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticeOrder
import OAI.NumberTheory.PiExponent.Polynomials.CompositePullbackCoefficient

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveNormalizationModel PiExponent.CurveModelPlaces
open PiExponent.CurveValuationCenter PiExponent.CurvePlaceCenter
open PiExponent.LocalSectionOrder PiExponent.WeightedLocalLattice
open PiExponent.ProjectiveLatticePullback PiExponent.WeightedPolynomialPole

namespace PiExponent.CurveGlobalCoordinateOrder


variable {E σ : Type} [Field E] [Algebra ℂ E] [Fintype σ]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
variable (g : parameterCurve f hf ⟶ ProjectiveO1.projectiveSpace ℂ σ)
variable (y : σ → E) (z : σ) (hz : y z = 1)
variable (hg : parameterCurveGenericPoint f hf ≫ g =
  ProjectiveLocalCoefficients.normalizedMap (algebraMap ℂ E) y z hz)
include hg

omit [Fintype σ] in
theorem coordinateSection_ne_zero (b : σ) (hb : y b ≠ 0) :
    pullbackSection g (ProjectiveO1.coordinateSection b) ≠ 0 := by
  have hex : ∃ e : (Scheme.Modules.pullback (parameterCurveGenericPoint f hf ≫ g)).obj
      (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf ≅ O (Spec (CommRingCat.of E)),
      localCoefficient e (pullbackSection (parameterCurveGenericPoint f hf ≫ g)
        (ProjectiveO1.coordinateSection b)) = y b := by
    rw [hg]
    obtain ⟨e, he⟩ := ProjectiveLocalCoefficients.exists_frame_coordinate_coefficients
      (algebraMap ℂ E) y z hz
    exact ⟨e, he b⟩
  obtain ⟨e, he⟩ := hex
  obtain ⟨e', he'⟩ := CompositePullbackCoefficient.exists_frame (parameterCurveGenericPoint f hf) g e
  have heq := congrArg (fun c => (Scheme.ΓSpecIso (CommRingCat.of E)).hom c)
    (he' (ProjectiveO1.coordinateSection b))
  change localCoefficient e' (pullbackSection (parameterCurveGenericPoint f hf)
    (pullbackSection g (ProjectiveO1.coordinateSection b))) =
    localCoefficient e (pullbackSection (parameterCurveGenericPoint f hf ≫ g)
      (ProjectiveO1.coordinateSection b)) at heq
  rw [he] at heq
  intro hs
  rw [hs] at heq
  have hz' : pullbackSection (parameterCurveGenericPoint f hf)
      (0 : O (parameterCurve f hf) ⟶
        (Scheme.Modules.pullback g).obj (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf) = 0 := by
    simp [pullbackSection]
  rw [hz', (localCoefficient_eq_zero_iff _ _).mpr rfl] at heq
  exact hb heq.symm

theorem coordinate_divisor_order (p : NormalizedPlace ℂ E) (i : σ) (hi : y i ≠ 0)
    (hspan : generatedLattice (PlaceValuationRing.ring p) y Finset.univ =
      Submodule.span (PlaceValuationRing.ring p) {y i})
    (b : σ) (hb : y b ≠ 0) :
    (CurvePlaceSectionDivisor.divisor f hf
      ((ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).pullback g)
      (pullbackSection g (ProjectiveO1.coordinateSection b))
      (coordinateSection_ne_zero f hf g y z hz hg b hb) p : ℤ) =
      coordinateOrder p.valuation (y b) - coordinateOrder p.valuation (y i) := by
  have hmap := CurveGlobalMonomialLocal.centerMorphism_eq_latticeProjectiveMap
    f hf g y z hz hg p i hi hspan
  have hex : ∃ e : (Scheme.Modules.pullback (centerMorphism f hf p ≫ g)).obj
      (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf ≅
        O (Spec (CommRingCat.of (PlaceValuationRing.ring p))),
      ((sectionOrder e (pullbackSection (centerMorphism f hf p ≫ g)
        (ProjectiveO1.coordinateSection b))).toNat : ℤ) =
        coordinateOrder p.valuation (y b) - coordinateOrder p.valuation (y i) := by
    rw [hmap, PlaceValuationRing.valuation_eq_fractionAddValuation]
    obtain ⟨e, he⟩ := ProjectiveLatticeOrder.exists_frame_coordinate_orders
      (algebraMap ℂ (PlaceValuationRing.ring p)) y i hi hspan
    exact ⟨e, he b hb⟩
  obtain ⟨e, he⟩ := hex
  obtain ⟨e', he'⟩ := CompositePullbackCoefficient.exists_frame (centerMorphism f hf p) g e
  erw [CurvePlaceSectionOrder.divisor_eq_local_order f hf _ _ _ p e']
  have heq := congrArg
    (fun c => (Scheme.ΓSpecIso (CommRingCat.of (PlaceValuationRing.ring p))).hom c)
    (he' (ProjectiveO1.coordinateSection b))
  change localCoefficient e' (pullbackSection (centerMorphism f hf p)
    (pullbackSection g (ProjectiveO1.coordinateSection b))) =
      localCoefficient e (pullbackSection (centerMorphism f hf p ≫ g)
        (ProjectiveO1.coordinateSection b)) at heq
  unfold sectionOrder at he ⊢
  exact (congrArg (fun c : PlaceValuationRing.ring p =>
    ((IsDiscreteValuationRing.addVal (PlaceValuationRing.ring p) c).toNat : ℤ)) heq).trans he

end PiExponent.CurveGlobalCoordinateOrder

end

end OAI
