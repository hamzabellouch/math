import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Intersection.ConeProjectivePoint
import OAI.NumberTheory.SiegelZeros.Structure.LaurentEvalOne

namespace OAI

namespace SiegelZeros

section
section
section
namespace WeightedTorusJets.Geometry

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem irrelevant_eq_ker_constantCoeff {K σ : Type*} [CommSemiring K] :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal =
      RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) := by
  ext p
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff,
    GradedRing.proj_apply]
  change (decomposition.decompose' p 0 : MvPolynomial σ K) = 0 ↔ constantCoeff p = 0
  rw [decomposition.decompose'_apply]
  rw [homogeneousComponent_zero, constantCoeff_eq, C_eq_zero]

theorem homogeneous_ideal_le_irrelevant {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (hproper : I ≠ ⊤) :
    I ≤ (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal := by
  rw [irrelevant_eq_ker_constantCoeff]
  intro p hp
  change constantCoeff p = 0
  by_contra hn
  have hC := homogeneousComponent_mem_of_mem hI hp 0
  rw [homogeneousComponent_zero] at hC
  exact hproper (I.eq_top_of_isUnit_mem hC ((isUnit_iff_ne_zero.mpr hn).map C))

theorem irrelevant_isMaximal {K σ : Type*} [Field K] :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal.IsMaximal := by
  rw [irrelevant_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective constantCoeff
    (fun a => ⟨C a, constantCoeff_C σ a⟩)

theorem projectiveSpectrum_lt_irrelevant {K σ : Type*} [Field K]
    (x : ProjectiveSpectrum (homogeneousSubmodule σ K)) :
    x.asHomogeneousIdeal.toIdeal <
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal := by
  refine lt_of_le_not_ge
    (homogeneous_ideal_le_irrelevant x.asHomogeneousIdeal.toIdeal
      x.asHomogeneousIdeal.isHomogeneous x.isPrime.ne_top) ?_
  exact x.not_irrelevant_le

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

theorem topologicalKrullDim_le_closure_image {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsInducing f) (Z : Set X) :
    topologicalKrullDim Z ≤ topologicalKrullDim (closure (f '' Z)) := by
  have hmem (x : Z) : f x ∈ closure (f '' Z) :=
    subset_closure ⟨x, x.property, rfl⟩
  exact ((hf.comp Topology.IsInducing.subtypeVal).codRestrict hmem).topologicalKrullDim_le

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open _root_.AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

universe uClosure

theorem coneProjective_zeroLocus_dimension
    {K σ : Type uClosure} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    topologicalKrullDim (ProjectiveSpectrum.zeroLocus
      (homogeneousSubmodule (Option σ) K) (coneIdeal p : Set (MvPolynomial (Option σ) K))) =
      ringKrullDim (MvPolynomial σ K ⧸ p) := by
  obtain ⟨d, hd, _⟩ := finiteType_dimension_trdeg (K := K)
    (A := MvPolynomial σ K ⧸ p)
  apply le_antisymm
  · rw [hd]
    let m := (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Option σ) K)).toIdeal
    let : m.IsMaximal := irrelevant_isMaximal
    apply projective_zeroLocus_dim_le_of_cone_dim _ (coneIdeal p) m
      projectiveSpectrum_lt_irrelevant d
    rw [coneIdeal_quotient_ringKrullDim, hd]
  · let : IsImmersion (affineIntoProj (k := K) (fun i : σ => X i)) :=
      affineIntoProj_isImmersion _ (fun f => ⟨f, aeval_X_left_apply f⟩)
    have h : topologicalKrullDim (PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K))) ≤
        topologicalKrullDim (closure ((fun x : PrimeSpectrum (MvPolynomial σ K) =>
          ((affineIntoProj (k := K) (fun i : σ => X i)) x :
            ProjectiveSpectrum (homogeneousSubmodule (Option σ) K))) ''
              PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K)))) :=
      topologicalKrullDim_le_closure_image
        (affineIntoProj (k := K) (fun i : σ => X i)).isEmbedding.isInducing
        (PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K)))
    rw [zeroLocus_topologicalKrullDim] at h
    exact h.trans_eq (congrArg
      (fun Z : Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) K)) =>
        topologicalKrullDim Z) (closure_affineIntoProj_zeroLocus p))

theorem affineIntoProj_closure_dimension
    {K σ : Type uClosure} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    topologicalKrullDim (closure ((affineIntoProj (k := K) (fun i : σ => X i)) ''
      PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K)))) =
      topologicalKrullDim (PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K))) := by
  rw [closure_affineIntoProj_zeroLocus]
  change topologicalKrullDim (ProjectiveSpectrum.zeroLocus
      (homogeneousSubmodule (Option σ) K) (coneIdeal p : Set (MvPolynomial (Option σ) K))) =
    topologicalKrullDim (PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K)))
  rw [coneProjective_zeroLocus_dimension, zeroLocus_topologicalKrullDim]

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open _root_.AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

universe uClosureCodim

theorem affineIntoProj_closure_height_add_dimension
    {K σ : Type uClosureCodim} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) +
      topologicalKrullDim (closure ((affineIntoProj (k := K) (fun i : σ => X i)) ''
        PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K)))) = Nat.card σ := by
  calc
    _ = (p.height : WithBot ℕ∞) +
        topologicalKrullDim (PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K))) :=
      congrArg (fun d : WithBot ℕ∞ => (p.height : WithBot ℕ∞) + d)
        (affineIntoProj_closure_dimension p)
    _ = Nat.card σ := by
      rw [zeroLocus_topologicalKrullDim,
        prime_height_add_quotient_dim_eq_of_finiteType (K := K)]
      simp

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open _root_.AlgebraicGeometry

theorem projective_component_of_isMinimalPrime
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (I : Ideal A)
    (q : ProjectiveSpectrum 𝒜) (hq : I.IsMinimalPrime q.asHomogeneousIdeal.toIdeal) :
    Maximal (fun V : Set (ProjectiveSpectrum 𝒜) => IsIrreducible V ∧
      V ⊆ ProjectiveSpectrum.zeroLocus 𝒜 (I : Set A))
      (closure ({q} : Set (ProjectiveSpectrum 𝒜))) := by
  let : QuasiSober (ProjectiveSpectrum 𝒜) := inferInstanceAs (QuasiSober (Proj 𝒜))
  refine ⟨⟨isGenericPoint_closure.isIrreducible, ?_⟩, ?_⟩
  · exact closure_minimal (Set.singleton_subset_iff.mpr hq.le)
      (ProjectiveSpectrum.isClosed_zeroLocus 𝒜 (I : Set A))
  · intro V hV hqV
    let y := hV.1.genericPoint
    have hy : IsGenericPoint y (closure V) := hV.1.isGenericPoint_genericPoint_closure
    have hIy : I ≤ y.asHomogeneousIdeal.toIdeal :=
      closure_minimal hV.2 (ProjectiveSpectrum.isClosed_zeroLocus 𝒜 (I : Set A)) hy.mem
    have hyq : y.asHomogeneousIdeal.toIdeal ≤ q.asHomogeneousIdeal.toIdeal := by
      apply (ProjectiveSpectrum.le_iff_mem_closure 𝒜 y q).mpr
      rw [hy.def]
      exact subset_closure (hqV (subset_closure (Set.mem_singleton q)))
    have hqy := hq.2 ⟨y.isPrime, hIy⟩ hyq
    have heq : y = q := le_antisymm hyq hqy
    rw [← heq, hy.def]
    exact subset_closure

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

open _root_.AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coneProjective_isComponent_of_local_radical
    {ι K σ : Type*} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ)
    (hf : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Maximal (fun V : Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) K)) =>
      IsIrreducible V ∧ V ⊆ ProjectiveSpectrum.zeroLocus
        (homogeneousSubmodule (Option σ) K) (paddedHomogenizedIdeal f n))
      (ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option σ) K) (coneIdeal p)) := by
  have h := projective_component_of_isMinimalPrime (homogeneousSubmodule (Option σ) K)
    (paddedHomogenizedIdeal f n) (coneProjectivePoint p)
    (coneIdeal_mem_minimalPrimes_padded p f n hf)
  rwa [closure_coneProjectivePoint] at h

universe uPaddedComponent

theorem affineIntoProj_closure_isComponent_of_local_radical
    {ι : Type*} {K σ : Type uPaddedComponent} [CommRing K]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : ι → MvPolynomial σ K) (n : ι → ℕ)
    (hf : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Maximal (fun V : Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) K)) =>
      IsIrreducible V ∧ V ⊆ ProjectiveSpectrum.zeroLocus
        (homogeneousSubmodule (Option σ) K) (paddedHomogenizedIdeal f n))
      (closure ((affineIntoProj (k := K) (fun i : σ => X i)) ''
        PrimeSpectrum.zeroLocus (p : Set (MvPolynomial σ K)))) := by
  exact (congrArg
    (fun Z : Set (ProjectiveSpectrum (homogeneousSubmodule (Option σ) K)) =>
      Maximal (fun V => IsIrreducible V ∧ V ⊆ ProjectiveSpectrum.zeroLocus
        (homogeneousSubmodule (Option σ) K) (paddedHomogenizedIdeal f n)) Z)
    (closure_affineIntoProj_zeroLocus p)).mpr
      (coneProjective_isComponent_of_local_radical p f n hf)

end WeightedTorusJets.Geometry

end
end

section
namespace WeightedTorusJets.Geometry

attribute [local instance] spec_stalk_isLocalRing

theorem spec_stalk_cotangent_eq_localization {R : Type*} [CommRing R]
    (q : PrimeSpectrum R) [IsRegularLocalRing (Localization.AtPrime q.asIdeal)] :
    Module.finrank (IsLocalRing.ResidueField
      ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q))
      (IsLocalRing.CotangentSpace ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q)) =
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)) := by
  have : IsRegularLocalRing ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q) :=
    IsRegularLocalRing.of_ringEquiv (AlgebraicGeometry.StructureSheaf.stalkIso R q).toRingEquiv
  have hs := ((IsRegularLocalRing.iff_finrank_cotangentSpace
    ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q)).mp inferInstance)
  have hl := ((IsRegularLocalRing.iff_finrank_cotangentSpace
    (Localization.AtPrime q.asIdeal)).mp inferInstance)
  exact_mod_cast hs.trans
    ((AlgebraicGeometry.StructureSheaf.stalkIso R q).toRingEquiv.ringKrullDim.symm.trans hl.symm)

theorem torus_stalk_cotangent_eq_codimension {K : Type*} [Field K] (n : ℕ)
    (q : PrimeSpectrum (Localization.Away
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))) :
    Module.finrank (IsLocalRing.ResidueField
      ((AlgebraicGeometry.Spec.structureSheaf (Localization.Away
        (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))).presheaf.stalk q))
      (IsLocalRing.CotangentSpace
        ((AlgebraicGeometry.Spec.structureSheaf (Localization.Away
          (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))).presheaf.stalk q)) =
      n - ((ringKrullDim (Localization.Away
        (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) ⧸ q.asIdeal)).unbotD 0).toNat := by
  have : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
    regular_localization_component (Submonoid.powers
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))) q.asIdeal
  rw [spec_stalk_cotangent_eq_localization, torus_component_cotangent_eq_codimension]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

attribute [local instance] spec_stalk_isLocalRing

theorem torus_generic_stalk_cotangent_eq_codimension {K : Type*} [Field K] (n : ℕ)
    (q : PrimeSpectrum (Localization.Away
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))))
    (V : Set (PrimeSpectrum (Localization.Away
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))))
    (hV : IsGenericPoint q V) :
    Module.finrank (IsLocalRing.ResidueField
      ((AlgebraicGeometry.Spec.structureSheaf (Localization.Away
        (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))).presheaf.stalk q))
      (IsLocalRing.CotangentSpace
        ((AlgebraicGeometry.Spec.structureSheaf (Localization.Away
          (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))).presheaf.stalk q)) =
      n - ((topologicalKrullDim V).unbotD 0).toNat := by
  rw [generic_component_topologicalKrullDim q V hV]
  exact torus_stalk_cotangent_eq_codimension n q

end WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets.Geometry

noncomputable def affineZeroScheme {R : Type*} [CommRing R] (I : Ideal R) : Scheme :=
  Spec (CommRingCat.of (R ⧸ I))

noncomputable def affineZeroSchemeι {R : Type*} [CommRing R] (I : Ideal R) :
    affineZeroScheme I ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

theorem affineZeroScheme_isClosedImmersion {R : Type*} [CommRing R] (I : Ideal R) :
    IsClosedImmersion (affineZeroSchemeι I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

noncomputable def quotientLocalizationEquiv {R : Type*} [CommRing R]
    (I : Ideal R) (q : PrimeSpectrum (R ⧸ I)) :
    Localization.AtPrime q.asIdeal ≃ₐ[R ⧸ I]
      (Localization.AtPrime (q.asIdeal.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap R (Localization.AtPrime (q.asIdeal.comap (Ideal.Quotient.mk I))))) := by
  have : IsLocalization q.asIdeal.primeCompl
      (Localization.AtPrime (q.asIdeal.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap R (Localization.AtPrime (q.asIdeal.comap (Ideal.Quotient.mk I))))) := by
    rw [← Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q.asIdeal]
    exact IsLocalization.of_surjective _ _
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl (by simp)
  exact IsLocalization.algEquiv q.asIdeal.primeCompl _ _

noncomputable def affineZeroSchemeStalkEquiv {R : Type*} [CommRing R]
    (I : Ideal R) (q : PrimeSpectrum (R ⧸ I)) :
    (affineZeroScheme I).presheaf.stalk q ≃+*
      (Localization.AtPrime (q.asIdeal.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap R (Localization.AtPrime (q.asIdeal.comap (Ideal.Quotient.mk I))))) :=
  (StructureSheaf.stalkIso (R ⧸ I) q).symm.toRingEquiv.trans
    (quotientLocalizationEquiv I q).toRingEquiv

theorem affineZeroScheme_range {R : Type*} [CommRing R] (I : Ideal R) :
    Set.range (affineZeroSchemeι I) = PrimeSpectrum.zeroLocus (R := R) I := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  simpa only [Ideal.mk_ker] using
    range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective

noncomputable def affineZeroSchemePoint {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    PrimeSpectrum (R ⧸ I) :=
  I.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨p, hp⟩

theorem affineZeroSchemePoint_comap {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    (affineZeroSchemePoint I p hp).asIdeal.comap (Ideal.Quotient.mk I) = p.asIdeal :=
  congrArg (fun q : PrimeSpectrum.zeroLocus (R := R) I => q.1.asIdeal)
    (I.primeSpectrumQuotientOrderIsoZeroLocus.apply_symm_apply ⟨p, hp⟩)

theorem affineZeroSchemePoint_image {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    affineZeroSchemeι I (affineZeroSchemePoint I p hp) = p :=
  PrimeSpectrum.ext (affineZeroSchemePoint_comap I p hp)

noncomputable def affineZeroSchemeStalkEquivAt {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    (affineZeroScheme I).presheaf.stalk (affineZeroSchemePoint I p hp) ≃+*
      (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal))) := by
  have e := affineZeroSchemeStalkEquiv I (affineZeroSchemePoint I p hp)
  change _ ≃+* (Localization.AtPrime
      (PrimeSpectrum.comap (Ideal.Quotient.mk I) (affineZeroSchemePoint I p hp)).asIdeal ⧸
      I.map (algebraMap R (Localization.AtPrime
        (PrimeSpectrum.comap (Ideal.Quotient.mk I) (affineZeroSchemePoint I p hp)).asIdeal))) at e
  have h : PrimeSpectrum.comap (Ideal.Quotient.mk I) (affineZeroSchemePoint I p hp) = p :=
    PrimeSpectrum.ext (affineZeroSchemePoint_comap I p hp)
  rw [h] at e
  exact e

theorem ringEquiv_self_length {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  let : Algebra R S := e.toRingHom.toAlgebra
  exact (LinearEquiv.ofBijective (Algebra.linearMap R S) e.bijective).length_eq.trans
    (Module.length_eq_of_surjective (M := S) e.surjective)

theorem affineZeroSchemeStalk_length {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    Module.length ((affineZeroScheme I).presheaf.stalk (affineZeroSchemePoint I p hp))
        ((affineZeroScheme I).presheaf.stalk (affineZeroSchemePoint I p hp)) =
      Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal))) :=
  (ringEquiv_self_length (affineZeroSchemeStalkEquivAt I p hp)).trans
    (Module.length_eq_of_surjective (M := Localization.AtPrime p.asIdeal ⧸
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)))
      Ideal.Quotient.mk_surjective).symm

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

noncomputable def affineZeroSchemeInclusion {R : Type*} [CommRing R]
    (I J : Ideal R) (hIJ : I ≤ J) : affineZeroScheme J ⟶ affineZeroScheme I :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hIJ))

theorem affineZeroSchemeInclusion_isClosedImmersion {R : Type*} [CommRing R]
    (I J : Ideal R) (hIJ : I ≤ J) : IsClosedImmersion (affineZeroSchemeInclusion I J hIJ) :=
  IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective hIJ)

theorem affineZeroSchemeInclusion_comp_ι {R : Type*} [CommRing R]
    (I J : Ideal R) (hIJ : I ≤ J) :
    affineZeroSchemeInclusion I J hIJ ≫ affineZeroSchemeι I = affineZeroSchemeι J := by
  unfold affineZeroSchemeInclusion affineZeroSchemeι affineZeroScheme
  rw [← Spec.map_comp]
  congr 1

theorem affineZeroSchemeInclusion_comp {R : Type*} [CommRing R]
    (I J L : Ideal R) (hIJ : I ≤ J) (hJL : J ≤ L) :
    affineZeroSchemeInclusion J L hJL ≫ affineZeroSchemeInclusion I J hIJ =
      affineZeroSchemeInclusion I L (hIJ.trans hJL) := by
  unfold affineZeroSchemeInclusion affineZeroScheme
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (Ideal.Quotient.factor_comp hIJ hJL)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem affineZeroSchemePoint_isMinimalPrime {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I.IsMinimalPrime p.asIdeal) :
    (⊥ : Ideal (R ⧸ I)).IsMinimalPrime (affineZeroSchemePoint I p hp.le).asIdeal := by
  change _ ∈ minimalPrimes (R ⧸ I)
  rw [← (Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective).mem_set_image,
    ← Ideal.minimalPrimes_eq_comap, affineZeroSchemePoint_comap]
  exact hp

theorem affineZeroSchemePoint_isGenericPoint_component {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I.IsMinimalPrime p.asIdeal) :
    ∃ V : Set (affineZeroScheme I),
      IsGenericPoint (affineZeroSchemePoint I p hp.le) V ∧ Maximal IsIrreducible V := by
  let q := affineZeroSchemePoint I p hp.le
  refine ⟨PrimeSpectrum.zeroLocus (q.asIdeal : Set (R ⧸ I)),
    prime_genericPoint_zeroLocus q, ?_⟩
  have h := zeroLocus_maximal_of_isMinimalPrime (⊥ : Ideal (R ⧸ I)) q
    (affineZeroSchemePoint_isMinimalPrime I p hp)
  change Maximal (fun V : Set (PrimeSpectrum (R ⧸ I)) => IsIrreducible V) _
  simpa only [PrimeSpectrum.zeroLocus_bot, Set.subset_univ, and_true] using h

theorem affineZeroSchemePoint_zeroLocus_image {R : Type*} [CommRing R]
    (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    affineZeroSchemeι I ''
        PrimeSpectrum.zeroLocus ((affineZeroSchemePoint I p hp).asIdeal : Set (R ⧸ I)) =
      PrimeSpectrum.zeroLocus (p.asIdeal : Set R) := by
  change PrimeSpectrum.comap (Ideal.Quotient.mk I) '' _ = _
  rw [image_comap_zeroLocus_eq_zeroLocus_comap (R ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective, affineZeroSchemePoint_comap]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

section TorusJetZeroScheme

variable {K : Type*} [Field K]

local notation "Poly" => MvPolynomial (Fin 4) K
local notation "Torus" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : Poly))

noncomputable def torusJetZeroScheme (c : Fin 3 → Fin 4 → K) (F : Poly)
    (t : Fin 3 → ℕ) (b : ℕ) : Scheme :=
  affineZeroScheme (rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b)

theorem torusJetZeroScheme_isClosedImmersion (c : Fin 3 → Fin 4 → K) (F : Poly)
    (t : Fin 3 → ℕ) (b : ℕ) :
    IsClosedImmersion (affineZeroSchemeι
      (rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b)) :=
  affineZeroScheme_isClosedImmersion _

noncomputable def torusJetZeroSchemeStalkEquiv (c : Fin 3 → Fin 4 → K) (F : Poly)
    (t : Fin 3 → ℕ) (b : ℕ) (q : PrimeSpectrum Torus)
    (hq : rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b ≤ q.asIdeal) :
    (torusJetZeroScheme c F t b).presheaf.stalk
        (affineZeroSchemePoint
          (rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b) q hq) ≃+*
      (Localization.AtPrime q.asIdeal ⧸
        (rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b).map
          (algebraMap Torus (Localization.AtPrime q.asIdeal))) :=
  affineZeroSchemeStalkEquivAt _ q hq

theorem torusJetZeroSchemeStalk_length (c : Fin 3 → Fin 4 → K) (F : Poly)
    (t : Fin 3 → ℕ) (b : ℕ) (q : PrimeSpectrum Torus)
    (hq : rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b ≤ q.asIdeal) :
    let Z := torusJetZeroScheme c F t b
    let η := affineZeroSchemePoint
      (rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b) q hq
    Module.length (Z.presheaf.stalk η) (Z.presheaf.stalk η) =
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⧸
          (rectangleJetIdeal (fun a ↦ algebraMap Poly Torus (invariantJet c a F)) t b).map
            (algebraMap Torus (Localization.AtPrime q.asIdeal))) :=
  affineZeroSchemeStalk_length _ q hq

end TorusJetZeroScheme
end WeightedTorusJets.Geometry

end
end

end SiegelZeros

end OAI
