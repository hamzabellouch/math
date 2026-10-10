import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Field
import OAI.NumberTheory.SiegelZeros.Hilbert.ConeHomogeneousEquations

namespace OAI

noncomputable section

namespace SiegelZeros

open CategoryTheory AlgebraicGeometry

namespace SiegelZerosAwei.Workers.W15

section

universe u
variable (R : Type u) [CommRing R] [IsDomain R]

noncomputable instance affineSpecFunctionFieldAlgebra :
    Algebra R (Spec (CommRingCat.of R)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)

instance affineSpecFunctionField_isFractionRing :
    IsFractionRing R (Spec (CommRingCat.of R)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of R)

abbrev NormalizationRing := integralClosure R (FractionRing R)

noncomputable instance normalizationRing_integrallyClosed :
    IsIntegrallyClosed (NormalizationRing R) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)

noncomputable instance normalizationRing_fractionRing :
    IsFractionRing (NormalizationRing R) (FractionRing R) :=
  integralClosure.isFractionRing_of_finite_extension (FractionRing R) (FractionRing R)

noncomputable abbrev AffineNormalization : Scheme := Spec (CommRingCat.of (NormalizationRing R))

instance affineNormalization_integral : IsIntegral (AffineNormalization R) := inferInstance

noncomputable def affineNormalizationMap :
    AffineNormalization R ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (NormalizationRing R)))

instance affineNormalizationMap_integral : IsIntegralHom (affineNormalizationMap R) := by
  apply IsIntegralHom.SpecMap_iff.mpr
  exact algebraMap_isIntegral_iff.mpr inferInstance

instance affineNormalizationMap_universallyClosed :
    UniversallyClosed (affineNormalizationMap R) := inferInstance

theorem affineNormalization_stalk_integrallyClosed (x : AffineNormalization R) :
    IsIntegrallyClosed ((AffineNormalization R).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := (show PrimeSpectrum (NormalizationRing R) from x).isPrime
  let : Algebra (CommRingCat.of (NormalizationRing R))
      ((AffineNormalization R).presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of (NormalizationRing R)) x
  let : IsLocalization x.asIdeal.primeCompl
      ((AffineNormalization R).presheaf.stalk x) :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (NormalizationRing R)) x
  exact isIntegrallyClosed_of_isLocalization ((AffineNormalization R).presheaf.stalk x)
    x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors

noncomputable def normalizationFunctionFieldEquiv :
    (AffineNormalization R).functionField ≃+* FractionRing R :=
  (IsLocalization.algEquiv (nonZeroDivisors (NormalizationRing R))
    (AffineNormalization R).functionField (FractionRing R)).toRingEquiv

theorem normalizationFunctionFieldEquiv_algebraMap (x : NormalizationRing R) :
    normalizationFunctionFieldEquiv R
        (algebraMap (NormalizationRing R) (AffineNormalization R).functionField x) =
      algebraMap (NormalizationRing R) (FractionRing R) x :=
  (IsLocalization.algEquiv (nonZeroDivisors (NormalizationRing R))
    (AffineNormalization R).functionField (FractionRing R)).commutes x

noncomputable def normalizationOriginalFunctionFieldEquiv :
    (AffineNormalization R).functionField ≃+* (Spec (CommRingCat.of R)).functionField :=
  (normalizationFunctionFieldEquiv R).trans
    (IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R)
      (Spec (CommRingCat.of R)).functionField).toRingEquiv

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u
variable {V P S : Scheme.{u}} (j : V ⟶ P) [QuasiCompact j]

theorem toImage_ker_eq_bot : j.toImage.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : P.affineOpens => ⟨j.imageι ⁻¹ᵁ U.1, U.2.preimage _⟩)
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U => ?_
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [← RingHom.injective_iff_ker_eq_bot]
  exact j.toImage_app_injective U

theorem image_integral [IsIntegral V] : IsIntegral j.image := by
  let : IsSchemeTheoreticallyDominant j.toImage := ⟨toImage_ker_eq_bot j⟩
  let : IsReduced j.image := IsSchemeTheoreticallyDominant.isReduced j.toImage
  let : IrreducibleSpace j.image := by
    rw [irreducibleSpace_def]
    convert ((IrreducibleSpace.isIrreducible_univ V).image _
      j.toImage.continuous.continuousOn).closure
    simpa using j.toImage.denseRange.closure_range.symm
  exact isIntegral_of_irreducibleSpace_of_isReduced _

instance image_integral_instance [IsIntegral V] : IsIntegral j.image := image_integral j

theorem image_range_eq_closure : Set.range j.imageι = closure (Set.range j) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

omit [QuasiCompact j] in
theorem image_proper (s : P ⟶ S) [IsProper s] : IsProper (j.imageι ≫ s) := inferInstance

noncomputable def imageFunctionFieldEquiv [IsIntegral V] [IsImmersion j] :
    j.image.functionField ≃+* V.functionField :=
  ((j.image.presheaf.stalkCongr
    (.of_eq (genericPoint_eq_of_isOpenImmersion j.toImage).symm)) ≪≫
      asIso (j.toImage.stalkMap (genericPoint V))).commRingCatIsoToRingEquiv

end SiegelZerosAwei.Workers.W15

namespace W58

variable (K : Type*) [Field K]

abbrev AmbientPolynomial := MvPolynomial (Fin 4) K

def coordinateProduct : AmbientPolynomial K := ∏ i : Fin 4, MvPolynomial.X i

abbrev TorusRing := Localization (Submonoid.powers (coordinateProduct K))

def coordinate (i : Fin 4) : TorusRing K :=
  algebraMap (AmbientPolynomial K) (TorusRing K) (MvPolynomial.X i)

theorem coordinate_isUnit (i : Fin 4) : IsUnit (coordinate K i) := by
  apply IsLocalization.Away.isUnit_of_dvd (coordinateProduct K)
  exact Finset.dvd_prod_of_mem (fun j : Fin 4 => (MvPolynomial.X j : AmbientPolynomial K))
    (Finset.mem_univ i)

def identityEvaluation : TorusRing K →+* K :=
  IsLocalization.Away.lift (coordinateProduct K)
    (g := MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : Fin 4 => 1)) (by
      simp [coordinateProduct])

@[simp] theorem identityEvaluation_coordinate (i : Fin 4) :
    identityEvaluation K (coordinate K i) = 1 := by
  simp [identityEvaluation, coordinate]

@[simp] theorem identityEvaluation_polynomial (f : AmbientPolynomial K) :
    identityEvaluation K (algebraMap (AmbientPolynomial K) (TorusRing K) f) =
      MvPolynomial.eval (fun _ : Fin 4 => 1) f := by
  exact IsLocalization.Away.lift_eq (coordinateProduct K)
    (g := MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : Fin 4 => 1))
    (by simp [coordinateProduct]) f

theorem ambient_dimension : ringKrullDim (AmbientPolynomial K) = 4 := by
  simp [AmbientPolynomial]

theorem torus_dimension_le_four : ringKrullDim (TorusRing K) ≤ 4 := by
  apply (ringKrullDim_le_iff_height_le 4).2
  intro p hp
  let : p.IsPrime := hp
  rw [← IsLocalization.height_under (Submonoid.powers (coordinateProduct K)) p]
  exact (ringKrullDim_le_iff_height_le 4).1 (le_of_eq (ambient_dimension K))
    inferInstance

abbrev GenericLocalRing (p : Ideal (TorusRing K)) [p.IsPrime] := Localization.AtPrime p

abbrev GenericCotangent (p : Ideal (TorusRing K)) [p.IsPrime] :=
  IsLocalRing.CotangentSpace (GenericLocalRing K p)

theorem generic_local_dimension (p : Ideal (TorusRing K)) [p.IsPrime] :
    ringKrullDim (GenericLocalRing K p) = p.height :=
  IsLocalization.AtPrime.ringKrullDim_eq_height p (GenericLocalRing K p)

theorem generic_local_dimension_le_four (p : Ideal (TorusRing K)) [p.IsPrime] :
    ringKrullDim (GenericLocalRing K p) ≤ 4 := by
  rw [generic_local_dimension]
  exact (ringKrullDim_le_iff_height_le 4).1 (torus_dimension_le_four K) inferInstance

end W58

namespace SiegelZerosAwei.Workers.W15

open AlgebraicGeometry

universe u
variable (k : Type u) [Field k]
variable (p : Ideal (SiegelZeros.W58.TorusRing k)) [p.IsPrime]

abbrev TorusSubvarietyRing := SiegelZeros.W58.TorusRing k ⧸ p

noncomputable abbrev TorusSubvariety : Scheme := Spec (CommRingCat.of (TorusSubvarietyRing k p))

instance torusSubvariety_integral : IsIntegral (TorusSubvariety k p) := inferInstance

noncomputable abbrev NormalizedTorusSubvariety : Scheme := AffineNormalization (TorusSubvarietyRing k p)

instance normalizedTorusSubvariety_integral :
    IsIntegral (NormalizedTorusSubvariety k p) := inferInstance

theorem normalizedTorusSubvariety_stalk_integrallyClosed (x : NormalizedTorusSubvariety k p) :
    IsIntegrallyClosed ((NormalizedTorusSubvariety k p).presheaf.stalk x) :=
  affineNormalization_stalk_integrallyClosed (TorusSubvarietyRing k p) x

noncomputable def torusNormalizationFunctionFieldEquiv :
    (NormalizedTorusSubvariety k p).functionField ≃+* (TorusSubvariety k p).functionField :=
  normalizationOriginalFunctionFieldEquiv (TorusSubvarietyRing k p)

noncomputable def torusCoordinateFunction (i : Fin 4) :
    (TorusSubvariety k p).functionField :=
  algebraMap (TorusSubvarietyRing k p) (TorusSubvariety k p).functionField
    (Ideal.Quotient.mk p (SiegelZeros.W58.coordinate k i))

theorem torusCoordinateFunction_ne_zero (i : Fin 4) :
    torusCoordinateFunction k p i ≠ 0 :=
  (((SiegelZeros.W58.coordinate_isUnit k i).map (Ideal.Quotient.mk p)).map
    (algebraMap (TorusSubvarietyRing k p) (TorusSubvariety k p).functionField)).ne_zero

noncomputable def normalizedTorusCoordinateFunction (i : Fin 4) :
    (NormalizedTorusSubvariety k p).functionField :=
  (torusNormalizationFunctionFieldEquiv k p).symm (torusCoordinateFunction k p i)

theorem normalizedTorusCoordinateFunction_identification (i : Fin 4) :
    torusNormalizationFunctionFieldEquiv k p (normalizedTorusCoordinateFunction k p i) =
      torusCoordinateFunction k p i :=
  (torusNormalizationFunctionFieldEquiv k p).apply_symm_apply _

theorem normalizedTorusCoordinateFunction_ne_zero (i : Fin 4) :
    normalizedTorusCoordinateFunction k p i ≠ 0 := by
  intro h
  apply torusCoordinateFunction_ne_zero k p i
  rw [← normalizedTorusCoordinateFunction_identification k p i, h, map_zero]

end SiegelZerosAwei.Workers.W15

namespace W58

variable (K : Type*) [Field K]

theorem torus_formallySmooth : Algebra.FormallySmooth K (TorusRing K) := by
  infer_instance

theorem torus_essFiniteType : Algebra.EssFiniteType K (TorusRing K) := by
  infer_instance

theorem torus_noetherian : IsNoetherianRing (TorusRing K) := by
  infer_instance

theorem generic_local_formallySmooth (p : Ideal (TorusRing K)) [p.IsPrime] :
    Algebra.FormallySmooth K (GenericLocalRing K p) := by
  infer_instance

theorem generic_local_essFiniteType (p : Ideal (TorusRing K)) [p.IsPrime] :
    Algebra.EssFiniteType K (GenericLocalRing K p) := by
  infer_instance

theorem generic_local_noetherian (p : Ideal (TorusRing K)) [p.IsPrime] :
    IsNoetherianRing (GenericLocalRing K p) := by
  infer_instance

theorem generic_cotangent_finite (p : Ideal (TorusRing K)) [p.IsPrime] :
    FiniteDimensional (IsLocalRing.ResidueField (GenericLocalRing K p))
      (GenericCotangent K p) := by
  infer_instance

theorem generic_residue_formallySmooth [PerfectField K]
    (p : Ideal (TorusRing K)) [p.IsPrime] :
    Algebra.FormallySmooth K (IsLocalRing.ResidueField (GenericLocalRing K p)) := by
  let := generic_local_essFiniteType K p
  let f : GenericLocalRing K p →ₐ[K]
      IsLocalRing.ResidueField (GenericLocalRing K p) :=
    { __ := IsLocalRing.residue (GenericLocalRing K p)
      commutes' := fun _ => rfl }
  let : Algebra.EssFiniteType K
      (IsLocalRing.ResidueField (GenericLocalRing K p)) :=
    Algebra.EssFiniteType.of_surjective
      (R := K) (S := GenericLocalRing K p)
      (T := IsLocalRing.ResidueField (GenericLocalRing K p)) f (by
        change Function.Surjective (IsLocalRing.residue (GenericLocalRing K p))
        exact IsLocalRing.residue_surjective (R := GenericLocalRing K p))
  exact Algebra.FormallySmooth.of_perfectField

theorem generic_regular_iff_cotangent_dimension (p : Ideal (TorusRing K)) [p.IsPrime] :
    IsRegularLocalRing (GenericLocalRing K p) ↔
      (Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
        (GenericCotangent K p) : WithBot ℕ∞) = p.height := by
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace,
    generic_local_dimension]

variable {k R S : Type*} [CommRing k] [CommRing R] [IsDomain R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra.FormallySmooth k R]

theorem smooth_kaehler_localization_injective (M : Submonoid R)
    [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) :
    Function.Injective (KaehlerDifferential.map k k R S) := by
  apply (IsLocalizedModule.injective_iff_isRegular M
    (KaehlerDifferential.map k k R S)).2
  intro c
  exact Module.Flat.isSMulRegular_of_isRegular
    (IsRegular.of_ne_zero (nonZeroDivisors.ne_zero (hM c.property)))

end W58

namespace W17.ProjectiveChart

open MvPolynomial HomogeneousLocalization

abbrev ProjectivePolynomial := MvPolynomial (Fin 5) ℂ
abbrev AffinePolynomial := MvPolynomial (Fin 4) ℂ
abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 5) ℂ

instance gradingGradedRing : GradedRing grading :=
  MvPolynomial.gradedAlgebra (σ := Fin 5) (R := ℂ)
abbrev ChartRing := HomogeneousLocalization.Away grading (X (0 : Fin 5))
abbrev FullLocalization := Localization.Away (X (0 : Fin 5) : ProjectivePolynomial)

def degreeZeroConstants : ℂ →+* grading 0 where
  toFun c := ⟨C c, MvPolynomial.isHomogeneous_C (Fin 5) c⟩
  map_one' := by apply Subtype.ext; exact map_one C
  map_zero' := by apply Subtype.ext; exact map_zero C
  map_add' c d := by apply Subtype.ext; exact map_add C c d
  map_mul' c d := by apply Subtype.ext; exact map_mul C c d

theorem degreeZeroConstants_bijective : Function.Bijective degreeZeroConstants := by
  constructor
  · intro c d h
    exact MvPolynomial.C_injective (Fin 5) ℂ (congrArg Subtype.val h)
  · intro p
    have hp : p.val.IsHomogeneous 0 := p.property
    have hc : p.val = C (p.val.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hp.totalDegree_le)
    exact ⟨p.val.coeff 0, Subtype.ext hc.symm⟩

def degreeZeroEquiv : ℂ ≃+* grading 0 :=
  RingEquiv.ofBijective degreeZeroConstants degreeZeroConstants_bijective

instance finiteType_over_degreeZero : Algebra.FiniteType (grading 0) ProjectivePolynomial := by
  let : IsScalarTower ℂ (grading 0) ProjectivePolynomial :=
    IsScalarTower.of_algebraMap_eq (R := ℂ) (S := grading 0)
      (A := ProjectivePolynomial) (fun c => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℂ (grading 0) ProjectivePolynomial

def chartConstants : ℂ →+* ChartRing :=
  (HomogeneousLocalization.fromZeroRingHom grading
    (Submonoid.powers (X (0 : Fin 5)))).comp degreeZeroConstants

instance chartAlgebra : Algebra ℂ ChartRing := chartConstants.toAlgebra

def polynomialDehom : ProjectivePolynomial →+* AffinePolynomial :=
  WeightedTorusJets.W22.dehomogenize.comp
    (MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv 4)).toRingHom

@[simp] theorem polynomialDehom_zeroCoordinate : polynomialDehom (X (0 : Fin 5)) = 1 := by
  simp [polynomialDehom, MvPolynomial.renameEquiv_apply]

@[simp] theorem polynomialDehom_coordinate (i : Fin 4) :
    polynomialDehom (X i.succ) = X i := by
  simp [polynomialDehom, MvPolynomial.renameEquiv_apply,
    WeightedTorusJets.W22.dehomogenize]

@[simp] theorem polynomialDehom_C (c : ℂ) : polynomialDehom (C c) = C c := by
  simp [polynomialDehom, MvPolynomial.renameEquiv_apply,
    WeightedTorusJets.W22.dehomogenize]

def localizationDehom : FullLocalization →+* AffinePolynomial :=
  IsLocalization.Away.lift (X (0 : Fin 5)) (g := polynomialDehom) (by simp)

@[simp] theorem localizationDehom_algebraMap (p : ProjectivePolynomial) :
    localizationDehom (algebraMap ProjectivePolynomial FullLocalization p) =
      polynomialDehom p := IsLocalization.Away.lift_eq _ _ _

theorem localizationDehom_fraction (n : ℕ) (p : ProjectivePolynomial) :
    localizationDehom (Localization.mk p
      ⟨X (0 : Fin 5) ^ n, ⟨n, rfl⟩⟩) = polynomialDehom p := by
  rw [Localization.mk_eq_mk']
  have h := congrArg localizationDehom
    (IsLocalization.mk'_spec (S := FullLocalization) p
      (⟨X (0 : Fin 5) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (X (0 : Fin 5))))
  simpa using h

def chartDehomRingHom : ChartRing →+* AffinePolynomial :=
  localizationDehom.comp (algebraMap ChartRing FullLocalization)

theorem chartDehom_fraction (n : ℕ) (p : ProjectivePolynomial)
    (hp : p ∈ grading (n • (1 : ℕ))) :
    chartDehomRingHom (HomogeneousLocalization.Away.mk grading
      (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 5)) n p hp) = polynomialDehom p := by
  change localizationDehom (Localization.mk p _) = polynomialDehom p
  exact localizationDehom_fraction n p

@[simp] theorem chartDehom_constants (c : ℂ) :
    chartDehomRingHom (chartConstants c) = C c := by
  change localizationDehom (Localization.mk (C c) (1 : Submonoid.powers
    (X (0 : Fin 5) : ProjectivePolynomial))) = C c
  rw [Localization.mk_one_eq_algebraMap, localizationDehom_algebraMap, polynomialDehom_C]

def chartDehom : ChartRing →ₐ[ℂ] AffinePolynomial where
  __ := chartDehomRingHom
  commutes' c := chartDehom_constants c

def chartCoordinate (i : Fin 4) : ChartRing :=
  HomogeneousLocalization.Away.mk grading
    (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 5)) 1 (X i.succ)
    (by simpa using MvPolynomial.isHomogeneous_X ℂ i.succ)

@[simp] theorem chartDehom_coordinate (i : Fin 4) :
    chartDehom (chartCoordinate i) = X i := by
  exact (chartDehom_fraction 1 (X i.succ) _).trans (polynomialDehom_coordinate i)

def chartPolynomialMap : AffinePolynomial →ₐ[ℂ] ChartRing :=
  MvPolynomial.aeval chartCoordinate

theorem chartDehom_comp_chartPolynomialMap :
    chartDehom.comp chartPolynomialMap = AlgHom.id ℂ AffinePolynomial := by
  ext i
  simp [chartPolynomialMap]

theorem chartDehom_surjective : Function.Surjective chartDehom := by
  intro p
  refine ⟨chartPolynomialMap p, ?_⟩
  exact congrArg (fun f : AffinePolynomial →ₐ[ℂ] AffinePolynomial => f p)
    chartDehom_comp_chartPolynomialMap

theorem polynomialDehom_eq_zero_of_homogeneous {p : ProjectivePolynomial} {n : ℕ}
    (hp : p.IsHomogeneous n) (hz : polynomialDehom p = 0) : p = 0 := by
  have hrename : (MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv 4) p).IsHomogeneous n :=
    hp.rename_isHomogeneous
  have hzero := WeightedTorusJets.W22.dehomogenize_eq_zero_of_isHomogeneous hrename hz
  apply (MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv 4)).injective
  simpa using hzero

theorem chartDehom_injective : Function.Injective chartDehom := by
  apply (injective_iff_map_eq_zero chartDehom.toRingHom).mpr
  intro z hz
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    grading (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 5)) z
  have hpn : p.IsHomogeneous n := by simpa using hp
  have hpzero : p = 0 := polynomialDehom_eq_zero_of_homogeneous hpn
    ((chartDehom_fraction n p hp).symm.trans hz)
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk grading n
    (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 5)) p hp,
    HomogeneousLocalization.val_zero, hpzero, Localization.mk_zero]

def chartEquiv : ChartRing ≃ₐ[ℂ] AffinePolynomial :=
  AlgEquiv.ofBijective chartDehom ⟨chartDehom_injective, chartDehom_surjective⟩

@[simp] theorem chartEquiv_coordinate (i : Fin 4) :
    chartEquiv (chartCoordinate i) = X i := chartDehom_coordinate i

open AlgebraicGeometry CategoryTheory

abbrev projectiveSpace : Scheme := AlgebraicGeometry.Proj grading
abbrev affineSpace : Scheme := Spec (CommRingCat.of AffinePolynomial)

def affineChartIso : affineSpace ≅ Spec (CommRingCat.of ChartRing) :=
  Scheme.Spec.mapIso chartEquiv.toRingEquiv.toCommRingCatIso.op

def affineChartEmbedding : affineSpace ⟶ projectiveSpace :=
  affineChartIso.hom ≫ AlgebraicGeometry.Proj.awayι grading (X (0 : Fin 5))
    (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 5)) (Nat.zero_lt_succ 0)

instance affineChartEmbedding_isOpenImmersion : IsOpenImmersion affineChartEmbedding := by
  unfold affineChartEmbedding AlgebraicGeometry.Proj.awayι
  infer_instance

theorem affineChartEmbedding_opensRange :
    affineChartEmbedding.opensRange = AlgebraicGeometry.Proj.basicOpen grading (X (0 : Fin 5)) := by
  have : IsOpenImmersion (AlgebraicGeometry.Proj.awayι grading (X (0 : Fin 5))
      (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 5)) (Nat.zero_lt_succ 0)) := by
    unfold AlgebraicGeometry.Proj.awayι
    infer_instance
  exact (Scheme.Hom.opensRange_comp_of_isIso affineChartIso.hom
    (AlgebraicGeometry.Proj.awayι grading (X (0 : Fin 5))
      (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 5)) (Nat.zero_lt_succ 0))).trans
    (AlgebraicGeometry.Proj.opensRange_awayι grading (X (0 : Fin 5))
      (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 5)) (Nat.zero_lt_succ 0))

def projectiveToBase : projectiveSpace ⟶ Spec (CommRingCat.of ℂ) :=
  AlgebraicGeometry.Proj.toSpecZero grading ≫ Spec.map (CommRingCat.ofHom degreeZeroConstants)

instance projectiveToBase_isProper : IsProper projectiveToBase := by
  have : IsIso (Spec.map (CommRingCat.ofHom degreeZeroConstants)) := by
    change IsIso (Scheme.Spec.mapIso degreeZeroEquiv.toCommRingCatIso.op).hom
    infer_instance
  dsimp [projectiveToBase]
  infer_instance

theorem affineChartEmbedding_toBase :
    affineChartEmbedding ≫ projectiveToBase =
      Spec.map (CommRingCat.ofHom (C : ℂ →+* AffinePolynomial)) := by
  simp only [affineChartEmbedding, projectiveToBase, Category.assoc,
    AlgebraicGeometry.Proj.awayι_toSpecZero_assoc grading (X (0 : Fin 5))
      (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 5)) (Nat.zero_lt_succ 0)]
  change Spec.map (CommRingCat.ofHom chartDehomRingHom) ≫
    (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom grading _)) ≫
      Spec.map (CommRingCat.ofHom degreeZeroConstants)) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact chartDehom_constants c

end W17.ProjectiveChart

open CategoryTheory AlgebraicGeometry
open SiegelZeros.W17.ProjectiveChart

namespace SiegelZerosAwei.Workers.W15

instance projectiveSpace_locallyNoetherian : IsLocallyNoetherian projectiveSpace :=
  LocallyOfFiniteType.isLocallyNoetherian projectiveToBase

noncomputable def torusAffineEmbedding :
    Spec (CommRingCat.of (SiegelZeros.W58.TorusRing ℂ)) ⟶ affineSpace :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (SiegelZeros.W58.AmbientPolynomial ℂ) (SiegelZeros.W58.TorusRing ℂ)))

instance torusAffineEmbedding_open : IsOpenImmersion torusAffineEmbedding :=
  IsOpenImmersion.of_isLocalization (SiegelZeros.W58.coordinateProduct ℂ)

variable (p : Ideal (SiegelZeros.W58.TorusRing ℂ)) [p.IsPrime]

noncomputable def torusSubvarietyEmbedding : TorusSubvariety ℂ p ⟶ projectiveSpace :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p)) ≫
    torusAffineEmbedding ≫ affineChartEmbedding

instance torusSubvarietyEmbedding_immersion : IsImmersion (torusSubvarietyEmbedding p) := by
  let := IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (SiegelZeros.W58.TorusRing ℂ)) p
  dsimp only [torusSubvarietyEmbedding]
  infer_instance

instance torusSubvarietyEmbedding_quasiCompact : QuasiCompact (torusSubvarietyEmbedding p) :=
  inferInstance

noncomputable abbrev TorusProjectiveClosure : Scheme := (torusSubvarietyEmbedding p).image

instance torusProjectiveClosure_integral : IsIntegral (TorusProjectiveClosure p) := inferInstance

noncomputable def torusProjectiveClosureToBase :
    TorusProjectiveClosure p ⟶ Spec (CommRingCat.of ℂ) :=
  (torusSubvarietyEmbedding p).imageι ≫ projectiveToBase

instance torusProjectiveClosure_proper : IsProper (torusProjectiveClosureToBase p) :=
  image_proper (torusSubvarietyEmbedding p) projectiveToBase

instance torusProjectiveClosure_locallyNoetherian :
    IsLocallyNoetherian (TorusProjectiveClosure p) :=
  LocallyOfFiniteType.isLocallyNoetherian (torusProjectiveClosureToBase p)

omit [p.IsPrime] in
theorem torusProjectiveClosure_range :
    Set.range (torusSubvarietyEmbedding p).imageι =
      closure (Set.range (torusSubvarietyEmbedding p)) :=
  image_range_eq_closure (torusSubvarietyEmbedding p)

noncomputable def torusProjectiveClosureFunctionFieldEquiv :
    (TorusProjectiveClosure p).functionField ≃+* (TorusSubvariety ℂ p).functionField :=
  imageFunctionFieldEquiv (torusSubvarietyEmbedding p)

end SiegelZerosAwei.Workers.W15

end SiegelZeros

end

end OAI
