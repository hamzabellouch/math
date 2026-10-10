import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

namespace OAI

/-!
# Scheme-theoretic meaning of the coordinate-ring formulation

An algebra equivalence with a polynomial ring yields an isomorphism to affine
space **over the coefficient field**. The quotient presentation also supplies a
closed immersion, so neither assertion is encoded by a bare bijection of points.
-/

noncomputable section

namespace StableCoordinate
namespace AffineGeometry

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B]

/-- The spectrum of a `k`-algebra, viewed as a scheme over `Spec k`. -/
def algebraSpec (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

/-- Contravariance takes an algebra equivalence to an actual scheme isomorphism. -/
def specIsoOfAlgEquiv (e : A ≃ₐ[k] B) :
    Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A) :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- This scheme isomorphism respects the coefficient base scheme. -/
theorem specIsoOfAlgEquiv_hom_over (e : A ≃ₐ[k] B) :
    (specIsoOfAlgEquiv e).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact e.commutes r

/-- The stronger isomorphism in the category of schemes over `Spec k`. -/
def algebraSpecIso (e : A ≃ₐ[k] B) : algebraSpec k B ≅ algebraSpec k A :=
  Over.isoMk (specIsoOfAlgEquiv e) (specIsoOfAlgEquiv_hom_over e)

/-- Full faithfulness of `Spec` recovers the ring map from every affine scheme isomorphism. -/
def ringEquivOfSpecIso
    (e : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A)) : A ≃+* B :=
  (Scheme.Spec.preimageIso e).unop.commRingCatIsoToRingEquiv

/-- The recovered ring equivalence is exactly the pullback of the original morphism. -/
theorem ringEquivOfSpecIso_apply
    (e : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A)) (a : A) :
    ringEquivOfSpecIso e a = Spec.preimage e.hom a := rfl

/-- Every affine scheme isomorphism over the coefficient base induces an algebra
isomorphism. Thus algebra automorphisms do not omit any ambient automorphisms. -/
def algEquivOfSpecIso
    (e : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k B))) : A ≃ₐ[k] B :=
  AlgEquiv.ofRingEquiv (f := ringEquivOfSpecIso e) (by
    intro r
    have h := congrArg Spec.preimage he
    rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map] at h
    exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of B => f r) h)

/-- In particular, every automorphism in the category of schemes over `Spec k`
is accounted for by an algebra automorphism. -/
def algEquivOfAlgebraSpecIso (e : algebraSpec k B ≅ algebraSpec k A) : A ≃ₐ[k] B :=
  algEquivOfSpecIso ((Over.forget _).mapIso e) e.hom.w

/-- Recovering the algebra map and applying `Spec` returns the given isomorphism. -/
theorem specIsoOfAlgEquiv_algEquivOfSpecIso
    (e : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k B))) :
    specIsoOfAlgEquiv (algEquivOfSpecIso e he) = e := by
  apply Iso.ext
  change Spec.map (Spec.preimage e.hom) = e.hom
  exact Spec.map_preimage e.hom

/-- The ring and scheme-over-base existence formulations are equivalent. -/
theorem nonempty_algEquiv_iff_algebraSpecIso :
    Nonempty (A ≃ₐ[k] B) ↔ Nonempty (algebraSpec k B ≅ algebraSpec k A) :=
  ⟨fun ⟨e⟩ => ⟨algebraSpecIso e⟩, fun ⟨e⟩ => ⟨algEquivOfAlgebraSpecIso e⟩⟩

/-- Transporting a defining ideal transports its closed subset by the associated
ambient scheme isomorphism (with the contravariant direction made explicit). -/
theorem specIso_image_zeroLocus_of_ideal_map
    (e : A ≃ₐ[k] B) (I : Ideal A) (J : Ideal B)
    (h : I.map e.toRingHom = J) :
    (specIsoOfAlgEquiv e.symm).hom ''
        PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (J : Set B) := by
  change PrimeSpectrum.comap e.symm.toRingHom '' PrimeSpectrum.zeroLocus (I : Set A) = _
  rw [image_comap_zeroLocus_eq_zeroLocus_comap _ _ e.symm.surjective]
  change PrimeSpectrum.zeroLocus (I.comap e.toRingEquiv.symm : Set B) = _
  rw [Ideal.comap_symm e.toRingEquiv]
  exact congrArg (fun K : Ideal B => PrimeSpectrum.zeroLocus (K : Set B)) h

/-- Conversely, equality of the closed subsets under any ambient scheme
isomorphism over the base recovers equality of their radical defining ideals. -/
theorem ideal_map_of_specIso_image_zeroLocus
    (I : Ideal B) (J : Ideal A) (hI : I.IsRadical) (hJ : J.IsRadical)
    (e : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (h : e.hom '' PrimeSpectrum.zeroLocus (I : Set B) =
      PrimeSpectrum.zeroLocus (J : Set A)) :
    I.map (algEquivOfSpecIso e he).symm.toRingHom = J := by
  let a := algEquivOfSpecIso e he
  have ha : Spec.map (CommRingCat.ofHom a.toRingHom) = e.hom := by
    exact congrArg Iso.hom (specIsoOfAlgEquiv_algEquivOfSpecIso e he)
  have hz : PrimeSpectrum.zeroLocus (I.comap a.toRingHom : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) := by
    rw [← image_comap_zeroLocus_eq_zeroLocus_comap B a.toRingHom a.surjective I]
    change Spec.map (CommRingCat.ofHom a.toRingHom) ''
      PrimeSpectrum.zeroLocus (I : Set B) = _
    rw [ha]
    exact h
  have hi : I.comap a.toRingHom = J := by
    have hz' := PrimeSpectrum.zeroLocus_eq_iff.mp hz
    rwa [(hI.comap a.toRingHom).radical, hJ.radical] at hz'
  change I.map a.toRingEquiv.symm = J
  rw [Ideal.map_symm a.toRingEquiv]
  exact hi

/-- For radical defining ideals, the algebraic orbit condition is equivalent to
the geometric orbit condition under **all** ambient automorphisms over the base. -/
theorem ideal_transport_iff_scheme_transport (I J : Ideal A)
    (hI : I.IsRadical) (hJ : J.IsRadical) :
    (∃ e : A ≃ₐ[k] A, I.map e.toRingHom = J) ↔
      ∃ e : Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of A),
        (e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
          Spec.map (CommRingCat.ofHom (algebraMap k A))) ∧
        e.hom '' PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨specIsoOfAlgEquiv e.symm, specIsoOfAlgEquiv_hom_over e.symm,
      specIso_image_zeroLocus_of_ideal_map e I J he⟩
  · rintro ⟨e, he, h⟩
    exact ⟨(algEquivOfSpecIso e he).symm,
      ideal_map_of_specIso_image_zeroLocus I J hI hJ e he h⟩

/-- A polynomial-ring algebra presentation gives affine space as a scheme,
not just its underlying collection of rational points. -/
def affineSpaceIsoOfAlgEquiv {σ : Type u} (e : A ≃ₐ[k] MvPolynomial σ k) :
    Spec (CommRingCat.of A) ≅ AffineSpace σ (Spec (CommRingCat.of k)) :=
  specIsoOfAlgEquiv e.symm ≪≫ (AffineSpace.SpecIso σ (CommRingCat.of k)).symm

/-- The polynomial presentation isomorphism is an isomorphism over `Spec k`. -/
theorem affineSpaceIsoOfAlgEquiv_hom_over {σ : Type u}
    (e : A ≃ₐ[k] MvPolynomial σ k) :
    (affineSpaceIsoOfAlgEquiv e).hom ≫
      (AffineSpace σ (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  simp only [affineSpaceIsoOfAlgEquiv, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    AffineSpace.SpecIso_inv_over]
  exact specIsoOfAlgEquiv_hom_over e.symm

/-- Scheme-over-base version of polynomial-ring coordinates. -/
def affineSpaceOverIsoOfAlgEquiv {σ : Type u}
    (e : A ≃ₐ[k] MvPolynomial σ k) :
    algebraSpec k A ≅ Over.mk
      (AffineSpace σ (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
  Over.isoMk (affineSpaceIsoOfAlgEquiv e) (affineSpaceIsoOfAlgEquiv_hom_over e)

/-- The natural map from the spectrum of a quotient into the ambient affine scheme. -/
def quotientEmbedding (I : Ideal A) :
    Spec (CommRingCat.of (A ⧸ I)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- This is genuinely a closed immersion. -/
instance quotientEmbedding_isClosedImmersion (I : Ideal A) :
    IsClosedImmersion (quotientEmbedding I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The embedded image is exactly the closed subset defined by the ideal. -/
theorem quotientEmbedding_range (I : Ideal A) :
    Set.range (quotientEmbedding I) = PrimeSpectrum.zeroLocus (I : Set A) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  simp

/-- In particular every algebra equivalence of a hypersurface coordinate ring
with a polynomial algebra gives the required affine-space isomorphism. -/
def hypersurfaceIsoOfAlgEquiv {σ τ : Type u}
    (p : MvPolynomial σ k)
    (e : (MvPolynomial σ k ⧸ Ideal.span {p}) ≃ₐ[k] MvPolynomial τ k) :
    Spec (CommRingCat.of (MvPolynomial σ k ⧸ Ideal.span {p})) ≅
      AffineSpace τ (Spec (CommRingCat.of k)) :=
  affineSpaceIsoOfAlgEquiv e

end AffineGeometry
end StableCoordinate

end

end OAI
