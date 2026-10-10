import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Determinants.GenericNormalization

namespace OAI

namespace SiegelZeros

noncomputable section
attribute [local instance] WeightedTorusJets.Geometry.polynomialGradedAlgebra
open Module
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open CategoryTheory _root_.AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
open CategoryTheory _root_.AlgebraicGeometry
open Polynomial IsLocalRing TensorProduct
namespace WeightedTorusJets

theorem transcendental_of_nonzero_nonunit
    {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    {t : A} (ht0 : t ≠ 0) (htu : ¬ IsUnit t) : Transcendental k t := by
  intro h
  exact htu (h.isIntegral.isUnit ht0)

theorem residue_aeval_eq_eval_zero
    {k A : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    {t : A} (ht : t ∈ maximalIdeal A) (p : k[X]) :
    residue A (Polynomial.aeval t p) = algebraMap k (ResidueField A) (p.eval 0) := by
  have ht0 : residue A t = 0 := (residue_eq_zero_iff t).mpr ht
  change (IsScalarTower.toAlgHom k A (ResidueField A)) (Polynomial.aeval t p) = _
  rw [← Polynomial.aeval_algHom_apply]
  change Polynomial.aeval (residue A t) p = _
  rw [ht0, ← Polynomial.coeff_zero_eq_aeval_zero', Polynomial.coeff_zero_eq_eval_zero]

theorem isUnit_aeval_of_eval_zero_ne_zero
    {k A : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    {t : A} (ht : t ∈ maximalIdeal A) {p : k[X]} (hp : p.eval 0 ≠ 0) :
    IsUnit (Polynomial.aeval t p) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval_eq_eval_zero ht]
  exact (_root_.map_ne_zero (algebraMap k (ResidueField A))).mpr hp

abbrev parameterIdeal (k : Type*) [Field k] : Ideal k[X] :=
  RingHom.ker (Polynomial.evalRingHom (0 : k))

instance parameterIdeal_isPrime (k : Type*) [Field k] : (parameterIdeal k).IsPrime :=
  RingHom.ker_isPrime _

abbrev parameterRing (k : Type*) [Field k] := Localization.AtPrime (parameterIdeal k)

theorem exists_parameter_local_algebra
    {k A : Type*} [Field k] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra k A] (t : A) (ht : Irreducible t) :
    ∃ φ : parameterRing k →ₐ[k] A,
      Function.Injective φ ∧ IsLocalHom φ.toRingHom ∧
      (maximalIdeal (parameterRing k)).map φ.toRingHom = maximalIdeal A := by
  let p := parameterIdeal k
  let R := Localization.AtPrime p
  have htmem : t ∈ maximalIdeal A := ht.not_isUnit
  let φ : R →ₐ[k] A := IsLocalization.liftAlgHom (M := p.primeCompl)
    (f := Polynomial.aeval t) fun s ↦ isUnit_aeval_of_eval_zero_ne_zero htmem s.property
  have hφ : φ.toRingHom.comp (algebraMap k[X] R) = (Polynomial.aeval t).toRingHom := by
    apply RingHom.ext
    intro r
    exact IsLocalization.lift_eq _ r
  have hinj : Function.Injective φ := by
    rw [show Function.Injective φ = Function.Injective φ.toRingHom from rfl,
      IsLocalization.injective_iff_map_algebraMap_eq p.primeCompl]
    intro x y
    simp only [← RingHom.comp_apply, hφ]
    change _ ↔ Polynomial.aeval t x = Polynomial.aeval t y
    exact (FaithfulSMul.algebraMap_injective k[X] R).eq_iff.trans
        ((transcendental_iff_injective.mp
          (transcendental_of_nonzero_nonunit ht.ne_zero ht.not_isUnit)).eq_iff).symm
  have hmap : (maximalIdeal R).map φ.toRingHom = maximalIdeal A := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hφ]
    have hp : p = Ideal.span {(Polynomial.X : k[X])} := by
      simpa [p, parameterIdeal] using Polynomial.ker_evalRingHom (0 : k)
    rw [hp, Ideal.map_span, Set.image_singleton]
    change Ideal.span {Polynomial.aeval t Polynomial.X} = maximalIdeal A
    rw [Polynomial.aeval_X, ht.maximalIdeal_eq]
  exact ⟨φ, hinj, ((local_hom_TFAE φ.toRingHom).out 3 1).mp hmap.le, hmap⟩

end WeightedTorusJets

open TensorProduct IsLocalRing

namespace WeightedTorusJets

theorem formallySmooth_of_flat_of_essFiniteType_of_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [Algebra.EssFiniteType R S] [PerfectField (ResidueField R)]
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Algebra.FormallySmooth R S := by
  let e : (ResidueField R ⊗[R] S) ≃+* ResidueField S :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R)).symm.toRingEquiv.trans
      (Ideal.quotEquivOfEq hmap)
  let : Field (ResidueField R ⊗[R] S) :=
    (e.toMulEquiv.isField (Field.toIsField (ResidueField S))).toField
  let P := Algebra.EssFiniteType.subalgebra R S
  let M := Algebra.EssFiniteType.submonoid R S
  have : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor M



theorem formallySmooth_of_essFiniteType_of_discreteValuationRing
    {k A : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra k A] [Algebra.EssFiniteType k A] :
    Algebra.FormallySmooth k A := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨φ, hinj, hlocal, hmap⟩ := exists_parameter_local_algebra (k := k) t ht
  let R := parameterRing k
  algebraize [φ.toRingHom]
  have : IsLocalHom (algebraMap R A) := hlocal
  have : Module.IsTorsionFree R A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Algebra.EssFiniteType R A := Algebra.EssFiniteType.of_comp k R A
  have : CharZero (ResidueField R) := Algebra.charZero_of_charZero k (ResidueField R)
  have : Algebra.FormallySmooth R A :=
    formallySmooth_of_flat_of_essFiniteType_of_map_maximalIdeal hmap
  have : Algebra.FormallyEtale k[X] R :=
    Algebra.FormallyEtale.of_isLocalization (parameterIdeal k).primeCompl
  have : Algebra.FormallySmooth k R := Algebra.FormallySmooth.comp k k[X] R
  exact Algebra.FormallySmooth.comp k R A

end WeightedTorusJets

open scoped TensorProduct

namespace WeightedTorusJets.Geometry

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

noncomputable def conormalDifferential (I : Ideal A) :
    I.Cotangent →ₗ[A ⧸ I] (A ⧸ I) ⊗[A] Ω[A⁄K] :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((KaehlerDifferential.kerCotangentToTensor K A (A ⧸ I)).comp
      (Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap A (A ⧸ I)))
        Ideal.mk_ker.symm).toLinearMap)

@[simp]
theorem conormalDifferential_toCotangent (I : Ideal A) (x : I) :
    conormalDifferential (K := K) I (I.toCotangent x) =
      1 ⊗ₜ[A] KaehlerDifferential.D K A x.val := by
  simp only [conormalDifferential, LinearMap.extendScalarsOfSurjective_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Ideal.Cotangent.equivOfEq_toCotangent,
    KaehlerDifferential.kerCotangentToTensor_toCotangent]
  rfl

theorem conormalDifferential_injective (I : Ideal A)
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (A ⧸ I)] :
    Function.Injective (conormalDifferential (K := K) I) := by
  have hi : Function.Injective (KaehlerDifferential.kerCotangentToTensor K A (A ⧸ I)) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
      (R := K) Ideal.Quotient.mk_surjective).mpr inferInstance
  exact hi.comp (Ideal.Cotangent.equivOfEq I
    (RingHom.ker (algebraMap A (A ⧸ I))) Ideal.mk_ker.symm).injective

theorem exists_derivation_residue_eq_one (I : Ideal A) [I.IsMaximal]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (A ⧸ I)]
    (x : I) (hx : I.toCotangent x ≠ 0) :
    ∃ D : Derivation K A A, Ideal.Quotient.mk I (D x) = 1 := by
  let := Ideal.Quotient.field I
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (A ⧸ I) hx
  obtain ⟨ψ, hψ⟩ := LinearMap.dualMap_surjective_of_injective
    (conormalDifferential_injective (K := K) I) φ
  let l : Ω[A⁄K] →ₗ[A] A ⧸ I := ψ.restrictScalars A ∘ₗ
    TensorProduct.mk A (A ⧸ I) Ω[A⁄K] 1
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (Algebra.linearMap A (A ⧸ I)) l
    Ideal.Quotient.mk_surjective
  refine ⟨KaehlerDifferential.linearMapEquivDerivation K A f, ?_⟩
  change Ideal.Quotient.mk I (f (KaehlerDifferential.D K A x)) = 1
  have he := LinearMap.congr_fun hf (KaehlerDifferential.D K A x)
  change Ideal.Quotient.mk I (f (KaehlerDifferential.D K A x)) =
    ψ (1 ⊗ₜ[A] KaehlerDifferential.D K A x) at he
  rw [he, ← conormalDifferential_toCotangent]
  exact (LinearMap.congr_fun hψ (I.toCotangent x)).trans hφ

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem uniformizer_cotangent_ne_zero {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (t : A) (ht : Irreducible t)
    (hm : t ∈ IsLocalRing.maximalIdeal A) :
    (IsLocalRing.maximalIdeal A).toCotangent ⟨t, hm⟩ ≠ 0 := by
  intro h
  have hd := ((IsLocalRing.maximalIdeal A).toCotangent_eq_zero ⟨t, hm⟩).mp h
  change t ∈ IsLocalRing.maximalIdeal A ^ 2 at hd
  rw [ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hd
  have hle : 2 ≤ 1 := (pow_dvd_pow_iff ht.ne_zero ht.not_isUnit).mp (by simpa using hd)
  omega

theorem exists_transverse_derivation_uniformizer {K A : Type*} [Field K] [PerfectField K]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra K A]
    [Algebra.EssFiniteType K A] [Algebra.FormallySmooth K A]
    (t : A) (ht : Irreducible t) :
    ∃ D : Derivation K A A, IsLocalRing.residue A (D t) = 1 := by
  have hm : t ∈ IsLocalRing.maximalIdeal A := by
    rw [ht.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton t)
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have : Algebra.FormallySmooth K (A ⧸ IsLocalRing.maximalIdeal A) := inferInstance
  exact exists_derivation_residue_eq_one (K := K) (IsLocalRing.maximalIdeal A)
    ⟨t, hm⟩ (uniformizer_cotangent_ne_zero t ht hm)



variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

noncomputable def localizeDerivation (M : Submonoid S) [IsLocalization M T]
    (D : Derivation R S S) : Derivation R T T :=
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  let d := (Algebra.ofId S T).toLinearMap.compDer D
  ((d.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

theorem localizeDerivation_algebraMap (M : Submonoid S) [IsLocalization M T]
    (D : Derivation R S S) (s : S) :
    localizeDerivation M D (algebraMap S T s) = algebraMap S T (D s) := by
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  change ((Algebra.ofId S T).toLinearMap.compDer D).liftKaehlerDifferential.liftBaseChange T
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
      (KaehlerDifferential.D R T (algebraMap S T s))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets

theorem int_coefficients_eq_zero_of_sum_eq_zero
    {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    {c : ι → K} (hc : LinearIndependent ℚ c)
    {n : ι → ℤ} (h : ∑ i, c i * (n i : K) = 0) : ∀ i, n i = 0 := by
  apply Fintype.linearIndependent_iff.mp (hc.restrict_scalars' ℤ) n
  simpa [zsmul_eq_mul, mul_comm] using h

theorem exists_unit_mul_zpow_order
    {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {t : X.presheaf.stalk x} (ht : Irreducible t)
    {f : X.functionField} (hf : f ≠ 0) :
    ∃ u : (X.presheaf.stalk x)ˣ,
      f = algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) *
        algebraMap (X.presheaf.stalk x) X.functionField t ^ X.ord f x := by
  have hf_order : Ring.ordFrac (X.presheaf.stalk x) f = WithZero.exp (X.ord f x) := by
    exact (AlgebraicGeometry.Scheme.ord_eq_iff hx hf).mp rfl
  have hpow : Ring.ordFrac (X.presheaf.stalk x)
      (algebraMap (X.presheaf.stalk x) X.functionField t ^ X.ord f x) =
      Ring.ordFrac (X.presheaf.stalk x) f := by
    rw [map_zpow₀, Ring.ordFrac_irreducible ht, hf_order, ← WithZero.exp_zsmul]
    simp
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := X.presheaf.stalk x)
    (algebraMap (X.presheaf.stalk x) X.functionField t ^ X.ord f x) f hpow
  exact ⟨u, by simpa [Units.smul_def, Algebra.smul_def] using hu.symm⟩



theorem log_deriv_mul_zpow
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (D : Derivation R K K) {u t : K} (hu : u ≠ 0) (ht : t ≠ 0) (n : ℤ) :
    D (u * t ^ n) / (u * t ^ n) = D u / u + (n : K) * (D t / t) := by
  rw [D.leibniz, D.leibniz_zpow]
  simp only [smul_eq_mul, zsmul_eq_mul, zpow_sub₀ ht, zpow_one]
  field_simp
  ring

theorem exists_rescaled_log_deriv_lift
    {R A K L : Type*} [CommRing R] [CommRing A] [Field K] [Field L]
    [Algebra R A] [Algebra R K]
    (φ : A →+* K) (ψ : A →+* L)
    (d : Derivation R A A) (D : Derivation R K K)
    (hD : ∀ a, D (φ a) = φ (d a))
    (u : Aˣ) (t : A) (n : ℤ) (ht : φ t ≠ 0)
    (hres_t : ψ t = 0) :
    ∃ a : A,
      φ a = φ t * (D (φ (u : A) * φ t ^ n) / (φ (u : A) * φ t ^ n)) ∧
      ψ a = (n : L) * ψ (d t) := by
  refine ⟨t * (↑(u⁻¹) : A) * d (u : A) + (n : A) * d t, ?_, ?_⟩
  · have hu : φ (u : A) ≠ 0 := (u.isUnit.map φ).ne_zero
    rw [log_deriv_mul_zpow D hu ht n, hD, hD]
    simp only [map_add, map_mul, map_intCast, map_units_inv]
    field_simp
  · simp [hres_t]

theorem sum_orders_eq_zero_of_kaehler_relation
    {ι k A F E : Type*} [Fintype ι] [Field k] [CommRing A] [Field F] [Field E]
    [Algebra k A] [Algebra k F] [Algebra k E]
    (φ : A →ₐ[k] F) (ψ : A →ₐ[k] E) (hφ : Function.Injective φ)
    (d : Derivation k A A) (D : Derivation k F F)
    (hD : ∀ a, D (φ a) = φ (d a))
    (u : ι → Aˣ) (t : A) (n : ι → ℤ) (c : ι → k) (ht : φ t ≠ 0)
    (hres_t : ψ t = 0) (hres_dt : ψ (d t) ≠ 0)
    (hω : ∑ i, (algebraMap k F (c i) / (φ (u i : A) * φ t ^ n i)) •
      KaehlerDifferential.D k F (φ (u i : A) * φ t ^ n i) = 0) :
    ∑ i, algebraMap k E (c i) * (n i : E) = 0 := by
  have hlog : ∑ i, algebraMap k F (c i) *
      (D (φ (u i : A) * φ t ^ n i) / (φ (u i : A) * φ t ^ n i)) = 0 := by
    simpa only [map_sum, map_smul, map_zero, Derivation.liftKaehlerDifferential_comp_D,
      smul_eq_mul, div_mul_eq_mul_div, mul_div_assoc] using
      congrArg D.liftKaehlerDifferential hω
  choose a ha hres using fun i =>
    exists_rescaled_log_deriv_lift φ.toRingHom ψ.toRingHom d D hD
      (u i) t (n i) ht hres_t
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at ha hres
  have hA : ∑ i, algebraMap k A (c i) * a i = 0 := by
    apply hφ
    simp only [map_sum, map_mul, AlgHom.commutes, map_zero]
    simp_rw [ha, mul_left_comm (algebraMap k F _) (φ t)]
    rw [← Finset.mul_sum, hlog, mul_zero]
  have hE : ∑ i, algebraMap k E (c i) * ((n i : E) * ψ (d t)) = 0 := by
    simpa only [map_sum, map_mul, AlgHom.commutes, map_zero, hres] using congrArg ψ hA
  simp_rw [← mul_assoc] at hE
  rw [← Finset.sum_mul] at hE
  exact (mul_eq_zero.mp hE).resolve_right hres_dt



theorem scheme_residue_equation_of_log_form
    {ι k : Type*} [Fintype ι] [Field k] [CharZero k]
    {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    [Algebra k (X.presheaf.stalk x)] [Algebra k X.functionField]
    [IsScalarTower k (X.presheaf.stalk x) X.functionField]
    [Algebra.EssFiniteType k (X.presheaf.stalk x)]
    (c : ι → k)
    {f : ι → X.functionField} (hf : ∀ i, f i ≠ 0)
    (hω : ∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) :
    ∑ i, c i * (X.ord (f i) x : k) = 0 := by
  let A := X.presheaf.stalk x
  have : Algebra.FormallySmooth k A :=
    formallySmooth_of_essFiniteType_of_discreteValuationRing
  let φ : A →ₐ[k] X.functionField := IsScalarTower.toAlgHom k A X.functionField
  let ψ : A →ₐ[k] IsLocalRing.ResidueField A :=
    IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨d, hd⟩ := Geometry.exists_transverse_derivation_uniformizer (K := k) t ht
  let D : Derivation k X.functionField X.functionField :=
    Geometry.localizeDerivation (nonZeroDivisors A) d
  have hD : ∀ a, D (φ a) = φ (d a) :=
    fun a => Geometry.localizeDerivation_algebraMap (nonZeroDivisors A) d a
  choose u hu using fun i => exists_unit_mul_zpow_order hx ht (hf i)
  have htφ : φ t ≠ 0 := by
    simpa only [φ, IsScalarTower.toAlgHom_apply, map_zero] using
      (IsFractionRing.injective A X.functionField).ne ht.ne_zero
  have hres_t : ψ t = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff t).mpr
    rw [IsLocalRing.mem_maximalIdeal]
    exact ht.not_isUnit
  have hres_dt : ψ (d t) ≠ 0 := by
    change IsLocalRing.residue A (d t) ≠ 0
    rw [hd]
    exact one_ne_zero
  have hω' : ∑ i, (algebraMap k X.functionField (c i) /
      (φ (u i : A) * φ t ^ X.ord (f i) x)) •
      KaehlerDifferential.D k X.functionField
        (φ (u i : A) * φ t ^ X.ord (f i) x) = 0 := by
    have hu' (i) : φ (u i : A) * φ t ^ X.ord (f i) x = f i := (hu i).symm
    simpa only [hu'] using hω
  apply (algebraMap k (IsLocalRing.ResidueField A)).injective
  simpa only [map_sum, map_mul, map_intCast, map_zero] using
    (sum_orders_eq_zero_of_kaehler_relation φ ψ (IsFractionRing.injective A X.functionField)
      d D hD u t (fun i => X.ord (f i) x) c htφ hres_t hres_dt hω')



universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem schemeBaseStalkAlgebra_essFiniteType {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (x : X) :
    let := schemeBaseStalkAlgebra f x
    Algebra.EssFiniteType R (X.presheaf.stalk x) := by
  change (schemeBaseToStalk f x).EssFiniteType
  have hbase : (StructureSheaf.toStalk R (f x)).hom.EssFiniteType := by
    let : Algebra R ((Spec.structureSheaf R).presheaf.stalk (f x)) :=
      StructureSheaf.stalkAlgebra R (f x)
    change Algebra.EssFiniteType R ((Spec.structureSheaf R).presheaf.stalk (f x))
    let q : PrimeSpectrum R := f x
    exact Algebra.EssFiniteType.of_isLocalization _ q.asIdeal.primeCompl
  exact hbase.comp (LocallyOfFiniteType.stalkMap f x)

theorem schemeBaseStalkAlgebra_isScalarTower {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    let := schemeBaseStalkAlgebra f x
    let : Algebra R X.functionField := schemeBaseStalkAlgebra f (genericPoint X)
    IsScalarTower R (X.presheaf.stalk x) X.functionField := by
  let := schemeBaseStalkAlgebra f x
  let : Algebra R X.functionField := schemeBaseStalkAlgebra f (genericPoint X)
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, by simp⟩⟩
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  change schemeBaseToStalk f (genericPoint X) a =
    algebraMap (X.presheaf.stalk x) X.functionField (schemeBaseToStalk f x a)
  simp only [schemeBaseToStalk_eq_global_germ, RingHom.comp_apply]
  exact (X.algebraMap_germ_eq_germToFunctionField (show x ∈ (⊤ : X.Opens) by simp) _).symm

end WeightedTorusJets

namespace WeightedTorusJets

universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem scheme_residue_equation_of_locallyOfFiniteType
    {ι : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    {x : X} (hx : Order.coheight x = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (c : ι → k) (f : ι → X.functionField) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    (∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) →
      ∑ i, c i * (X.ord (f i) x : k) = 0 := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro hω
  let := schemeBaseStalkAlgebra p x
  have : Algebra.EssFiniteType k (X.presheaf.stalk x) :=
    schemeBaseStalkAlgebra_essFiniteType p x
  have : IsScalarTower k (X.presheaf.stalk x) X.functionField :=
    schemeBaseStalkAlgebra_isScalarTower p x
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    Scheme.isDiscreteValuationRing_stalk_of_isIntegrallyClosed hx
  exact scheme_residue_equation_of_log_form hx c hf hω

theorem scheme_orders_zero_of_locallyOfFiniteType_log_form
    {ι : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (c : ι → k) (hc : LinearIndependent ℚ c)
    (f : ι → X.functionField) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    (∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) →
      ∀ i, X.ord (f i) = 0 := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro hω i
  funext x
  change X.ord (f i) x = 0
  by_cases hx : Order.coheight x = 1
  · exact int_coefficients_eq_zero_of_sum_eq_zero hc
      (scheme_residue_equation_of_locallyOfFiniteType p hx c f hf hω) i
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx (f i)

theorem scheme_global_units_of_locallyOfFiniteType_log_form
    {ι : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (c : ι → k) (hc : LinearIndependent ℚ c)
    (f : ι → X.functionField) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    (∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) →
      ∀ i, ∃ s : Γ(X, ⊤), IsUnit s ∧
        X.presheaf.germ ⊤ (genericPoint X) (by simp) s = f i := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro hω i
  apply Scheme.exists_global_unit_of_ord_eq_zero (f i) (hf i)
  intro x
  exact congrFun (scheme_orders_zero_of_locallyOfFiniteType_log_form p c hc f hf hω i) x

end WeightedTorusJets

end

end SiegelZeros

end OAI
