import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterOverlapProjection : Spec (.of (parameterLaurentChart f hf)) ⟶
    Spec (.of (LaurentPolynomial F)) :=
  letI := parameterLaurentAlgebra f hf
  Spec.map (CommRingCat.ofHom (algebraMap (LaurentPolynomial F) (parameterLaurentChart f hf)))

@[reassoc] theorem zeroOverlap_projection :
    zeroOverlap f hf ≫ parameterChartProjection f hf =
      parameterOverlapProjection f hf ≫ ProjectiveLine.zeroChartOverlap F := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  unfold zeroOverlap parameterChartProjection parameterOverlapProjection
    ProjectiveLine.zeroChartOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply F[X] (LaurentPolynomial F) E p

@[reassoc] theorem infinityOverlap_projection :
    infinityOverlap f hf ≫ parameterChartProjection f⁻¹ (transcendental_inverse f hf) =
      parameterOverlapProjection f hf ≫ ProjectiveLine.infinityChartOverlap F := by
  let := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
  let := parameterLaurentAlgebra f hf
  unfold infinityOverlap parameterChartProjection parameterOverlapProjection
    ProjectiveLine.infinityChartOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    apply Subtype.ext
    change algebraMap F[X] E (Polynomial.C c) =
      parameterLaurentMap f hf (ProjectiveLine.infinityPolynomialMap F (Polynomial.C c))
    rw [parameterPolynomialAlgebra_map]
    simp [parameterLaurentMap, LaurentPolynomial.eval₂_C]
  · apply Subtype.ext
    change algebraMap F[X] E Polynomial.X =
      parameterLaurentMap f hf (ProjectiveLine.infinityPolynomialMap F Polynomial.X)
    rw [parameterPolynomialAlgebra_map]
    simp

def parameterCurveProjection : parameterCurve f hf ⟶ ProjectiveLine.projectiveLine F :=
  Limits.pushout.desc
    (parameterChartProjection f hf ≫ ProjectiveLine.chartMap F false)
    (parameterChartProjection f⁻¹ (transcendental_inverse f hf) ≫
      ProjectiveLine.chartMap F true) (by
      rw [zeroOverlap_projection_assoc, infinityOverlap_projection_assoc]
      rw [ProjectiveLine.reciprocalChart_compatibility])

@[reassoc] theorem zeroChart_projection :
    zeroChartInclusion f hf ≫ parameterCurveProjection f hf =
      parameterChartProjection f hf ≫ ProjectiveLine.chartMap F false :=
  Limits.pushout.inl_desc _ _ _

@[reassoc] theorem infinityChart_projection :
    infinityChartInclusion f hf ≫ parameterCurveProjection f hf =
      parameterChartProjection f⁻¹ (transcendental_inverse f hf) ≫
        ProjectiveLine.chartMap F true :=
  Limits.pushout.inr_desc _ _ _

theorem parameterCurveProjection_preimage_zero :
    parameterCurveProjection f hf ⁻¹ᵁ (ProjectiveLine.chartMap F false).opensRange =
      (zeroChartInclusion f hf).opensRange := by
  ext x
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · change parameterCurveProjection f hf (zeroChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F false).opensRange ↔
        zeroChartInclusion f hf q ∈ Set.range (zeroChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, zeroChart_projection, Scheme.Hom.comp_apply]
    exact iff_of_true ⟨_, rfl⟩ ⟨q, rfl⟩
  · change parameterCurveProjection f hf (infinityChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F false).opensRange ↔
        infinityChartInclusion f hf q ∈ Set.range (zeroChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, infinityChart_projection, Scheme.Hom.comp_apply,
      infinityChart_mem_zero_iff]
    change parameterChartProjection f⁻¹ (transcendental_inverse f hf) q ∈
      (ProjectiveLine.chartMap F true ⁻¹ᵁ (ProjectiveLine.chartMap F (!true)).opensRange) ↔ _
    rw [ProjectiveLine.chartMap_preimage_other]
    let := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
    change q ∈ PrimeSpectrum.basicOpen
      (algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf)) Polynomial.X) ↔ _
    rw [infinityOverlap_range]
    rfl

theorem parameterCurveProjection_preimage_infinity :
    parameterCurveProjection f hf ⁻¹ᵁ (ProjectiveLine.chartMap F true).opensRange =
      (infinityChartInclusion f hf).opensRange := by
  ext x
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · change parameterCurveProjection f hf (zeroChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F true).opensRange ↔
        zeroChartInclusion f hf q ∈ Set.range (infinityChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, zeroChart_projection, Scheme.Hom.comp_apply,
      zeroChart_mem_infinity_iff]
    change parameterChartProjection f hf q ∈
      (ProjectiveLine.chartMap F false ⁻¹ᵁ (ProjectiveLine.chartMap F (!false)).opensRange) ↔ _
    rw [ProjectiveLine.chartMap_preimage_other]
    let := parameterPolynomialAlgebra f hf
    change q ∈ PrimeSpectrum.basicOpen
      (algebraMap F[X] (parameterChart f hf) Polynomial.X) ↔ _
    rw [zeroOverlap_range]
    rfl
  · change parameterCurveProjection f hf (infinityChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F true).opensRange ↔
        infinityChartInclusion f hf q ∈ Set.range (infinityChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, infinityChart_projection, Scheme.Hom.comp_apply]
    exact iff_of_true ⟨_, rfl⟩ ⟨q, rfl⟩

theorem zeroChartProjection_isPullback :
    IsPullback (zeroChartInclusion f hf) (parameterChartProjection f hf)
      (parameterCurveProjection f hf) (ProjectiveLine.chartMap F false) :=
  (IsOpenImmersion.isPullback _ _ _ _ (zeroChart_projection f hf)
    (parameterCurveProjection_preimage_zero f hf)).flip

theorem infinityChartProjection_isPullback :
    IsPullback (infinityChartInclusion f hf)
      (parameterChartProjection f⁻¹ (transcendental_inverse f hf))
      (parameterCurveProjection f hf) (ProjectiveLine.chartMap F true) :=
  (IsOpenImmersion.isPullback _ _ _ _ (infinityChart_projection f hf)
    (parameterCurveProjection_preimage_infinity f hf)).flip

instance parameterCurveProjection_isFinite [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsFinite (parameterCurveProjection f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let hAffine := AlgebraicGeometry.IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop.{u}
  let : IsZariskiLocalAtTarget (@AlgebraicGeometry.IsFinite.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hAffine
  apply IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.IsFinite.{u})
    (ProjectiveLine.affineChartCover F)
  intro i
  cases i
  · change IsFinite (Limits.pullback.snd (parameterCurveProjection f hf)
      (ProjectiveLine.chartMap F false))
    rw [← (zeroChartProjection_isPullback f hf).isoPullback_inv_snd]
    infer_instance
  · change IsFinite (Limits.pullback.snd (parameterCurveProjection f hf)
      (ProjectiveLine.chartMap F true))
    rw [← (infinityChartProjection_isPullback f hf).isoPullback_inv_snd]
    infer_instance

def parameterCurveStructureMap : parameterCurve f hf ⟶ Spec (.of F) :=
  parameterCurveProjection f hf ≫ ProjectiveLine.structureMap F

instance parameterCurveStructureMap_isProper [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsProper (parameterCurveStructureMap f hf) := by
  unfold parameterCurveStructureMap
  infer_instance

end PiExponent.CurveNormalizationModel

end

end OAI
