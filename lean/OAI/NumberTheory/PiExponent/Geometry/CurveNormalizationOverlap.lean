import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

theorem zeroOverlap_range :
    letI := parameterPolynomialAlgebra f hf
    Set.range (zeroOverlap f hf) =
      (PrimeSpectrum.basicOpen (algebraMap F[X] (parameterChart f hf) Polynomial.X) :
        Set (PrimeSpectrum (parameterChart f hf))) := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  let : Algebra (parameterChart f hf) (parameterLaurentChart f hf) :=
    (parameterChartOverlapHom f hf).toAlgebra
  have hX : algebraMap F[X] E Polynomial.X = f := by
    rw [parameterPolynomialAlgebra_map]; simp
  have : IsLocalization.Away f E := IsLocalization.of_le_isUnit (by
    rintro x ⟨n, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hf.ne_zero).pow n)
  have : IsLocalization.Away (algebraMap F[X] E Polynomial.X) E := by
    simpa only [hX] using (inferInstance : IsLocalization.Away f E)
  have : IsLocalization.Away (algebraMap F[X] (parameterChart f hf) Polynomial.X)
      (parameterLaurentChart f hf) :=
    integralClosureTower_isLocalizationAway (S := LaurentPolynomial F) (E := E) Polynomial.X
  exact PrimeSpectrum.localization_away_comap_range _ _

theorem infinityOverlap_range :
    letI := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
    Set.range (infinityOverlap f hf) =
      (PrimeSpectrum.basicOpen
        (algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf)) Polynomial.X) :
        Set (PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)))) := by
  let e := (reciprocalLaurentChartEquiv f hf).symm
  have : IsIso (CommRingCat.ofHom e.toRingHom) :=
    inferInstanceAs (IsIso e.toCommRingCatIso.hom)
  let g := Spec.map (CommRingCat.ofHom e.toRingHom)
  have : IsIso g :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom)
  have hfac : infinityOverlap f hf =
      g ≫ zeroOverlap f⁻¹ (transcendental_inverse f hf) := by
    unfold infinityOverlap zeroOverlap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hrange : Set.range (infinityOverlap f hf) =
      Set.range (zeroOverlap f⁻¹ (transcendental_inverse f hf)) := by
    rw [hfac]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨g z, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := g.surjective z
      exact ⟨w, rfl⟩
  exact hrange.trans (zeroOverlap_range f⁻¹ (transcendental_inverse f hf))

theorem infinityChart_mem_zero_iff
    (x : Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))) :
    infinityChartInclusion f hf x ∈ Set.range (zeroChartInclusion f hf) ↔
      x ∈ Set.range (infinityOverlap f hf) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, fi, fj, z, hzi, hzj⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (Limits.span (zeroOverlap f hf) (infinityOverlap f hf))).mp hy
    cases k with
    | none =>
      refine ⟨z, ?_⟩
      have he : fj = Limits.WalkingSpan.Hom.snd := Subsingleton.elim _ _
      simpa only [he, Limits.span_map_snd] using hzj
    | some k =>
      cases k with
      | left =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.left) (some Limits.WalkingPair.right) from fj)
      | right =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.right) (some Limits.WalkingPair.left) from fi)
  · rintro ⟨z, rfl⟩
    refine ⟨zeroOverlap f hf z, ?_⟩
    exact congrArg (fun g => g z) (parameterCurve_overlap_compatibility f hf)

theorem zeroChart_mem_infinity_iff
    (x : Spec (.of (parameterChart f hf))) :
    zeroChartInclusion f hf x ∈ Set.range (infinityChartInclusion f hf) ↔
      x ∈ Set.range (zeroOverlap f hf) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, fi, fj, z, hzi, hzj⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (Limits.span (zeroOverlap f hf) (infinityOverlap f hf))).mp hy.symm
    cases k with
    | none =>
      refine ⟨z, ?_⟩
      have he : fi = Limits.WalkingSpan.Hom.fst := Subsingleton.elim _ _
      simpa only [he, Limits.span_map_fst] using hzi
    | some k =>
      cases k with
      | left =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.left) (some Limits.WalkingPair.right) from fj)
      | right =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.right) (some Limits.WalkingPair.left) from fi)
  · rintro ⟨z, rfl⟩
    refine ⟨infinityOverlap f hf z, ?_⟩
    exact congrArg (fun g => g z) (parameterCurve_overlap_compatibility f hf).symm

end PiExponent.CurveNormalizationModel

end

end OAI
