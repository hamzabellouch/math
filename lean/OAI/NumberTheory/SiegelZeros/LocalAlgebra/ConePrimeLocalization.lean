import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.TensorProduct.Quotient

namespace OAI

namespace SiegelZeros

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

noncomputable section
namespace WeightedTorusJets.W25

open TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B]

theorem simple_baseChange_of_map_maximalIdeal
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    IsSimpleModule B (B ⊗[A] M) := by
  obtain ⟨J, hJ, ⟨e⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := A) (M := M)).mp inferInstance
  have hJmax : J = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hJ
  subst J
  have : IsSimpleModule B (B ⧸ IsLocalRing.maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (inferInstance : (IsLocalRing.maximalIdeal B).IsMaximal))
  let eB : (B ⊗[A] M) ≃ₗ[B] (B ⧸ IsLocalRing.maximalIdeal B) :=
    (e.baseChange A B M (A ⧸ IsLocalRing.maximalIdeal A)).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
        (IsLocalRing.maximalIdeal A)).toLinearEquiv.symm.trans
        (Submodule.quotEquivOfEq _ _ hmax))
  exact IsSimpleModule.congr eB

theorem length_baseChange_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    Module.length B (B ⊗[A] M) = Module.length A M := by
  induction hM with
  | of_subsingleton =>
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    have : IsSimpleModule B (B ⊗[A] (M ⧸ N)) :=
      simple_baseChange_of_map_maximalIdeal hmax
    have hexact : Function.Exact N.subtype N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]
    have hinj : Function.Injective (N.subtype.baseChange B) :=
      Module.Flat.lTensor_preserves_injective_linearMap N.subtype
        (Submodule.subtype_injective N)
    have hsurj : Function.Surjective (N.mkQ.baseChange B) :=
      LinearMap.lTensor_surjective B (Submodule.mkQ_surjective N)
    have hbaseexact : Function.Exact (N.subtype.baseChange B) (N.mkQ.baseChange B) :=
      Module.Flat.lTensor_exact B hexact
    have hA := Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hexact
    have hB := Module.length_eq_add_of_exact (N.subtype.baseChange B)
      (N.mkQ.baseChange B) hinj hsurj hbaseexact
    calc
      Module.length B (B ⊗[A] M) =
          Module.length B (B ⊗[A] N) + Module.length B (B ⊗[A] (M ⧸ N)) := hB
      _ = Module.length A N + Module.length A (M ⧸ N) := by
        rw [ih, Module.length_eq_one B (B ⊗[A] (M ⧸ N)),
          Module.length_eq_one A (M ⧸ N)]
      _ = Module.length A M := hA.symm

theorem finiteLength_baseChange_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    IsFiniteLength B (B ⊗[A] M) := by
  apply Module.length_ne_top_iff.mp
  rw [length_baseChange_of_flat_local hmax hM]
  exact Module.length_ne_top_iff.mpr hM

theorem length_quotient_map_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (I : Ideal A) (hI : IsFiniteLength A (A ⧸ I)) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  calc
    Module.length B (B ⧸ I.map (algebraMap A B)) =
        Module.length B (B ⊗[A] (A ⧸ I)) :=
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq
    _ = Module.length A (A ⧸ I) := length_baseChange_of_flat_local hmax hI

end WeightedTorusJets.W25

end


namespace WeightedTorusJets.W22

theorem length_eq_of_semilinear_bijective
    {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]
    (σ : R →+* S) [RingHomSurjective σ]
    (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

theorem quotient_length_eq_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : J = I.map e.toRingHom) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) := by
  let eQ : R ⧸ I ≃+* S ⧸ J := Ideal.quotientEquiv I J e hIJ
  let f : (R ⧸ I) →ₛₗ[e.toRingHom] (S ⧸ J) :=
    { toFun := eQ
      map_add' := eQ.map_add
      map_smul' := by
        intro r x
        change eQ ((Ideal.Quotient.mk I r) * x) =
          Ideal.Quotient.mk J (e r) * eQ x
        rw [map_mul]
        rfl }
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  exact length_eq_of_semilinear_bijective e.toRingHom f eQ.bijective

end WeightedTorusJets.W22


noncomputable section

namespace W17.ConeLocalLength

section ExtendedPrime

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]

theorem localized_maximalIdeal_map_eq (hQ : Q = P.map (algebraMap A B)) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) =
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P),
    Ideal.map_map, ← IsScalarTower.algebraMap_eq A (Localization.AtPrime P)
      (Localization.AtPrime Q),
    IsScalarTower.algebraMap_eq A B (Localization.AtPrime Q), ← Ideal.map_map, ← hQ]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal Q (Localization.AtPrime Q)

theorem localized_flat [Module.Flat A B] :
    Module.Flat (Localization.AtPrime P) (Localization.AtPrime Q) := inferInstance

end ExtendedPrime

section PolynomialExtension

variable (A : Type*) [CommRing A] (P : Ideal A) [P.IsPrime]

abbrev polynomialPrime : Ideal (Polynomial A) := P.map Polynomial.C

omit [P.IsPrime] in
theorem polynomialPrime_comap :
    (polynomialPrime A P).comap (algebraMap A (Polynomial A)) = P := by
  ext a
  change Polynomial.C a ∈ P.map Polynomial.C ↔ a ∈ P
  rw [Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro ha n
    by_cases hn : n = 0
    · subst n
      simpa using ha
    · simp [Polynomial.coeff_C, hn]

instance polynomialPrime_liesOver : (polynomialPrime A P).LiesOver P :=
  (Ideal.liesOver_iff _ _).mpr (polynomialPrime_comap A P).symm

theorem polynomialLocal_flat :
    Module.Flat (Localization.AtPrime P)
      (Localization.AtPrime (polynomialPrime A P)) := inferInstance

theorem polynomialLocal_maximalIdeal_map_eq :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (algebraMap (Localization.AtPrime P)
        (Localization.AtPrime (polynomialPrime A P))) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (polynomialPrime A P)) :=
  localized_maximalIdeal_map_eq P (polynomialPrime A P) rfl

end PolynomialExtension

section LaurentExtension

variable (A : Type*) [CommRing A] (P : Ideal A) [P.IsPrime]

abbrev laurentPrime : Ideal (LaurentPolynomial A) := P.map LaurentPolynomial.C

instance laurent_polynomial_tower : IsScalarTower A (Polynomial A) (LaurentPolynomial A) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    simp [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_eq,
      ← LaurentPolynomial.C_eq_algebraMap])

theorem polynomialPrime_disjoint_powers_X :
    Disjoint (Submonoid.powers (Polynomial.X : Polynomial A) : Set (Polynomial A))
      (polynomialPrime A P : Set (Polynomial A)) := by
  apply Set.disjoint_left.mpr
  rintro f ⟨n, rfl⟩ hf
  have hc := (Ideal.mem_map_C_iff.mp hf) n
  exact P.one_notMem (by simpa using hc)

omit [P.IsPrime] in
theorem laurentPrime_eq_map_polynomialPrime :
    laurentPrime A P = (polynomialPrime A P).map
      (algebraMap (Polynomial A) (LaurentPolynomial A)) := by
  have hc : (algebraMap (Polynomial A) (LaurentPolynomial A)).comp
      (Polynomial.C : A →+* Polynomial A) = LaurentPolynomial.C := by
    apply RingHom.ext
    intro a
    exact Polynomial.toLaurent_C a
  change P.map LaurentPolynomial.C =
    (P.map Polynomial.C).map (algebraMap (Polynomial A) (LaurentPolynomial A))
  rw [Ideal.map_map, hc]

instance laurentPrime_isPrime : (laurentPrime A P).IsPrime := by
  rw [laurentPrime_eq_map_polynomialPrime]
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (Polynomial.X : Polynomial A)) (LaurentPolynomial A)
    (polynomialPrime A P) inferInstance (polynomialPrime_disjoint_powers_X A P)

theorem laurentPrime_comap :
    (laurentPrime A P).comap (algebraMap A (LaurentPolynomial A)) = P := by
  rw [IsScalarTower.algebraMap_eq A (Polynomial A) (LaurentPolynomial A),
    ← Ideal.comap_comap, laurentPrime_eq_map_polynomialPrime]
  change (((polynomialPrime A P).map
    (algebraMap (Polynomial A) (LaurentPolynomial A))).under (Polynomial A)).comap
      (algebraMap A (Polynomial A)) = P
  rw [IsLocalization.under_map_of_isPrime_disjoint
    (Submonoid.powers (Polynomial.X : Polynomial A)) (LaurentPolynomial A)
    (show (polynomialPrime A P).IsPrime from inferInstance)
    (polynomialPrime_disjoint_powers_X A P)]
  exact polynomialPrime_comap A P

instance laurentPrime_liesOver : (laurentPrime A P).LiesOver P :=
  (Ideal.liesOver_iff _ _).mpr (laurentPrime_comap A P).symm

instance laurent_flat : Module.Flat A (LaurentPolynomial A) := by
  let : Module.Flat (Polynomial A) (LaurentPolynomial A) :=
    IsLocalization.flat (LaurentPolynomial A) (Submonoid.powers (Polynomial.X : Polynomial A))
  exact Module.Flat.trans A (Polynomial A) (LaurentPolynomial A)

theorem laurentLocal_flat :
    Module.Flat (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime A P)) := inferInstance

theorem laurentLocal_maximalIdeal_map_eq :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (algebraMap (Localization.AtPrime P)
        (Localization.AtPrime (laurentPrime A P))) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (laurentPrime A P)) :=
  localized_maximalIdeal_map_eq P (laurentPrime A P) rfl

theorem laurentLocal_quotient_length
    (I : Ideal (Localization.AtPrime P))
    (hI : IsFiniteLength (Localization.AtPrime P) (Localization.AtPrime P ⧸ I)) :
    Module.length (Localization.AtPrime (laurentPrime A P))
      (Localization.AtPrime (laurentPrime A P) ⧸ I.map
        (algebraMap (Localization.AtPrime P)
          (Localization.AtPrime (laurentPrime A P)))) =
    Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ I) :=
  WeightedTorusJets.W25.length_quotient_map_of_flat_local
    (laurentLocal_maximalIdeal_map_eq A P) I hI

end LaurentExtension


variable (k σ : Type*) [CommRing k]

abbrev AffineRing := MvPolynomial σ k
abbrev ConeRing := MvPolynomial (Option σ) k
abbrev ConeAway := Localization.Away (MvPolynomial.X none : ConeRing k σ)
abbrev LaurentChart := LaurentPolynomial (AffineRing k σ)

def coneHomogenizingUnit : (ConeAway k σ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := ConeAway k σ) (MvPolynomial.X none : ConeRing k σ)).unit

@[simp] theorem coneHomogenizingUnit_val :
    (coneHomogenizingUnit k σ : ConeAway k σ) =
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) :=
  IsUnit.unit_spec _

@[simp] theorem coneHomogenizingUnit_inv_mul :
    (↑(coneHomogenizingUnit k σ)⁻¹ : ConeAway k σ) *
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) = 1 := by
  rw [← coneHomogenizingUnit_val]
  exact Units.inv_mul (coneHomogenizingUnit k σ)

def affineToConeAway : AffineRing k σ →+* ConeAway k σ :=
  MvPolynomial.eval₂Hom
    ((algebraMap (ConeRing k σ) (ConeAway k σ)).comp MvPolynomial.C)
    (fun i => algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X (some i)) *
      ↑(coneHomogenizingUnit k σ)⁻¹)

@[simp] theorem affineToConeAway_C (a : k) :
    affineToConeAway k σ (MvPolynomial.C a) =
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.C a) := by
  simp [affineToConeAway]

@[simp] theorem affineToConeAway_X (i : σ) :
    affineToConeAway k σ (MvPolynomial.X i) =
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X (some i)) *
        ↑(coneHomogenizingUnit k σ)⁻¹ := by
  simp [affineToConeAway]

def coneToLaurent : ConeRing k σ →+* LaurentChart k σ :=
  MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp MvPolynomial.C)
    (fun i => i.elim (LaurentPolynomial.T 1)
      (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1))

@[simp] theorem coneToLaurent_C (a : k) :
    coneToLaurent k σ (MvPolynomial.C a) =
      LaurentPolynomial.C (MvPolynomial.C a) := by simp [coneToLaurent]

@[simp] theorem coneToLaurent_X_none :
    coneToLaurent k σ (MvPolynomial.X none) = LaurentPolynomial.T 1 := by
  simp [coneToLaurent]

@[simp] theorem coneToLaurent_X_some (i : σ) :
    coneToLaurent k σ (MvPolynomial.X (some i)) =
      LaurentPolynomial.C (MvPolynomial.X i) * LaurentPolynomial.T 1 := by
  simp [coneToLaurent]

def coneAwayToLaurent : ConeAway k σ →+* LaurentChart k σ :=
  IsLocalization.Away.lift (MvPolynomial.X none : ConeRing k σ)
    (g := coneToLaurent k σ) (by simpa using LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1)

@[simp] theorem coneAwayToLaurent_algebraMap (p : ConeRing k σ) :
    coneAwayToLaurent k σ (algebraMap (ConeRing k σ) (ConeAway k σ) p) =
      coneToLaurent k σ p := by simp [coneAwayToLaurent]

def laurentToConeAway : LaurentChart k σ →+* ConeAway k σ :=
  LaurentPolynomial.eval₂ (affineToConeAway k σ) (coneHomogenizingUnit k σ)

@[simp] theorem laurentToConeAway_C (p : AffineRing k σ) :
    laurentToConeAway k σ (LaurentPolynomial.C p) = affineToConeAway k σ p := by
  simp [laurentToConeAway]

@[simp] theorem laurentToConeAway_T :
    laurentToConeAway k σ (LaurentPolynomial.T 1) = coneHomogenizingUnit k σ := by
  simp [laurentToConeAway]

theorem laurentToConeAway_comp_coneToLaurent :
    (laurentToConeAway k σ).comp (coneToLaurent k σ) =
      algebraMap (ConeRing k σ) (ConeAway k σ) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    cases i with
    | none => simp
    | some i => simp [mul_assoc]

theorem laurentToConeAway_comp_coneAwayToLaurent :
    (laurentToConeAway k σ).comp (coneAwayToLaurent k σ) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ))
  apply RingHom.ext
  intro p
  change laurentToConeAway k σ
    (coneAwayToLaurent k σ (algebraMap _ _ p)) = algebraMap _ _ p
  rw [coneAwayToLaurent_algebraMap]
  exact RingHom.congr_fun (laurentToConeAway_comp_coneToLaurent k σ) p

theorem coneAwayToLaurent_comp_affineToConeAway :
    (coneAwayToLaurent k σ).comp (affineToConeAway k σ) = LaurentPolynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    change coneAwayToLaurent k σ (affineToConeAway k σ (MvPolynomial.X i)) =
      LaurentPolynomial.C (MvPolynomial.X i)
    apply (LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1).mul_left_inj.mp
    have hu : coneAwayToLaurent k σ (coneHomogenizingUnit k σ) =
        LaurentPolynomial.T 1 := by simp
    calc
      coneAwayToLaurent k σ (affineToConeAway k σ (MvPolynomial.X i)) *
          LaurentPolynomial.T 1 =
          coneAwayToLaurent k σ
            (affineToConeAway k σ (MvPolynomial.X i) * coneHomogenizingUnit k σ) := by
        rw [map_mul, hu]
      _ = LaurentPolynomial.C (MvPolynomial.X i) * LaurentPolynomial.T 1 := by
        simp [mul_assoc]

theorem coneAwayToLaurent_comp_laurentToConeAway :
    (coneAwayToLaurent k σ).comp (laurentToConeAway k σ) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Polynomial.X : Polynomial (AffineRing k σ)))
  apply Polynomial.ringHom_ext
  · intro a
    change coneAwayToLaurent k σ
      (laurentToConeAway k σ (algebraMap _ _ (Polynomial.C a))) =
        algebraMap _ _ (Polynomial.C a)
    simp only [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C,
      laurentToConeAway_C]
    exact RingHom.congr_fun (coneAwayToLaurent_comp_affineToConeAway k σ) a
  · change coneAwayToLaurent k σ
      (laurentToConeAway k σ (algebraMap _ _ Polynomial.X)) =
        algebraMap _ _ Polynomial.X
    simp [LaurentPolynomial.algebraMap_eq_toLaurent]

def coneLaurentEquiv : ConeAway k σ ≃+* LaurentChart k σ :=
  RingEquiv.ofRingHom (coneAwayToLaurent k σ) (laurentToConeAway k σ)
    (coneAwayToLaurent_comp_laurentToConeAway k σ)
    (laurentToConeAway_comp_coneAwayToLaurent k σ)

end W17.ConeLocalLength

end


namespace WeightedTorusJets.W22

variable {A : Type*} [CommRing A]

noncomputable def localPrimeTowerEquiv
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))) ≃ₐ[A]
      Localization.AtPrime p :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization Q.primeCompl p

@[simp] theorem localPrimeTowerEquiv_algebraMap
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (a : A) :
    localPrimeTowerEquiv Q p
      (algebraMap A (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))) a) =
      algebraMap A (Localization.AtPrime p) a :=
  (localPrimeTowerEquiv Q p).commutes a

theorem localPrimeTower_map_ideal
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (I : Ideal A) :
    (I.map (algebraMap A (Localization.AtPrime Q))).map
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime p)) =
    (I.map (algebraMap A
      (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))))).map
        (localPrimeTowerEquiv Q p).toRingEquiv.toRingHom := by
  have he : (localPrimeTowerEquiv Q p).toRingEquiv.toRingHom.comp
      (algebraMap A (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))))) =
      algebraMap A (Localization.AtPrime p) := by
    ext a
    exact localPrimeTowerEquiv_algebraMap Q p a
  rw [Ideal.map_map, Ideal.map_map, he,
    ← IsScalarTower.algebraMap_eq A (Localization.AtPrime Q) (Localization.AtPrime p)]

theorem localPrimeTower_quotient_length
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (I : Ideal A) :
    Module.length (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))))
      (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))) ⧸
        I.map (algebraMap A
          (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))))) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ (I.map (algebraMap A (Localization.AtPrime Q))).map
        (algebraMap (Localization.AtPrime Q) (Localization.AtPrime p))) :=
  quotient_length_eq_of_ringEquiv (localPrimeTowerEquiv Q p).toRingEquiv _ _
    (localPrimeTower_map_ideal Q p I)

end WeightedTorusJets.W22



namespace WeightedTorusJets.W22

variable {R S : Type*} [CommRing R] [CommRing S]

theorem primeCompl_map_eq_of_comap
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) :
    P.primeCompl.map e.toMonoidHom = Q.primeCompl := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change e r ∉ Q
    intro h
    apply hr
    rw [hPQ]
    exact h
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change e.symm x ∉ P
    rw [hPQ]
    change e (e.symm x) ∉ Q
    simpa only [e.apply_symm_apply] using (show x ∉ Q from hx)

noncomputable def primeLocalizationEquiv
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) :
    Localization.AtPrime P ≃+* Localization.AtPrime Q :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime Q)
    e (primeCompl_map_eq_of_comap e P Q hPQ)

theorem primeLocalizationEquiv_map_ideal
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) (I : Ideal R) :
    (I.map (algebraMap R (Localization.AtPrime P))).map
      (primeLocalizationEquiv e P Q hPQ).toRingHom =
    (I.map e.toRingHom).map (algebraMap S (Localization.AtPrime Q)) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext r
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (primeCompl_map_eq_of_comap e P Q hPQ) r

theorem localized_quotient_length_eq_of_ringEquiv
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) (I : Ideal R) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) =
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (I.map e.toRingHom).map
        (algebraMap S (Localization.AtPrime Q))) :=
  quotient_length_eq_of_ringEquiv (primeLocalizationEquiv e P Q hPQ)
    (I.map (algebraMap R (Localization.AtPrime P)))
    ((I.map e.toRingHom).map (algebraMap S (Localization.AtPrime Q)))
    (primeLocalizationEquiv_map_ideal e P Q hPQ I).symm

end WeightedTorusJets.W22



namespace WeightedTorusJets.W22

variable {A : Type*} [CommRing A]

def MinimalParentsBelow (I Q : Ideal A) := {P : Ideal A // P ∈ I.minimalPrimes ∧ P ≤ Q}

noncomputable instance minimalParentsBelow_fintype [IsNoetherianRing A] (I Q : Ideal A) :
    Fintype (MinimalParentsBelow I Q) := by
  have hfinite : {P : Ideal A | P ∈ I.minimalPrimes ∧ P ≤ Q}.Finite :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).subset (fun _ h => h.1)
  exact hfinite.fintype

instance {I Q : Ideal A} (P : MinimalParentsBelow I Q) : P.val.IsPrime := P.property.1.1.1

noncomputable def localizedMinimalPrimesEquiv (I Q : Ideal A) [Q.IsPrime] :
    (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes ≃ MinimalParentsBelow I Q := by
  classical
  let L := Localization.AtPrime Q
  let e := IsLocalization.AtPrime.orderIsoOfPrime L Q
  let f : (I.map (algebraMap A L)).minimalPrimes → MinimalParentsBelow I Q := fun p =>
    ⟨p.val.comap (algebraMap A L), by
      have hmin : p.val.comap (algebraMap A L) ∈ I.minimalPrimes :=
        (Set.ext_iff.mp (IsLocalization.minimalPrimes_map Q.primeCompl L I) p.val).mp p.property
      exact ⟨hmin, (e ⟨p.val, p.property.1.1⟩).property.2⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    apply Subtype.ext
    apply (IsLocalization.orderEmbedding Q.primeCompl L).injective
    exact congrArg Subtype.val h
  · intro P
    let p := e.symm ⟨P.val, P.property.1.1.1, P.property.2⟩
    have heq : p.val.comap (algebraMap A L) = P.val :=
      congrArg Subtype.val (e.apply_symm_apply ⟨P.val, P.property.1.1.1, P.property.2⟩)
    have hp : p.val ∈ (I.map (algebraMap A L)).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl L I]
      change p.val.comap (algebraMap A L) ∈ I.minimalPrimes
      rw [heq]
      exact P.property.1
    exact ⟨⟨p.val, hp⟩, Subtype.ext heq⟩

@[simp] theorem localizedMinimalPrimesEquiv_apply
    (I Q : Ideal A) [Q.IsPrime]
    (p : (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes) :
    (localizedMinimalPrimesEquiv I Q p).val =
      p.val.comap (algebraMap A (Localization.AtPrime Q)) := rfl

end WeightedTorusJets.W22


noncomputable section

namespace W17.ConeLocalLength

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

def awayChartPrime : Ideal (ConeAway k σ) :=
  (laurentPrime (AffineRing k σ) P).comap (coneLaurentEquiv k σ).toRingHom

instance awayChartPrime_isPrime : (awayChartPrime k σ P).IsPrime := by
  unfold awayChartPrime
  infer_instance

def conePrime : Ideal (ConeRing k σ) :=
  (awayChartPrime k σ P).comap (algebraMap (ConeRing k σ) (ConeAway k σ))

instance conePrime_isPrime : (conePrime k σ P).IsPrime := by
  unfold conePrime
  infer_instance

theorem homogenizing_coordinate_not_mem_conePrime :
    (MvPolynomial.X none : ConeRing k σ) ∉ conePrime k σ P := by
  intro h
  change algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) ∈
    awayChartPrime k σ P at h
  exact (show (awayChartPrime k σ P).IsPrime from inferInstance).ne_top
    ((awayChartPrime k σ P).eq_top_of_isUnit_mem h
      (IsLocalization.Away.algebraMap_isUnit (S := ConeAway k σ)
        (MvPolynomial.X none : ConeRing k σ)))

def conePrimeLocalizationEquiv :
    Localization.AtPrime (conePrime k σ P) ≃+*
      Localization.AtPrime (laurentPrime (AffineRing k σ) P) :=
  (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ))
    (awayChartPrime k σ P)).toRingEquiv.trans
      (WeightedTorusJets.W22.primeLocalizationEquiv (coneLaurentEquiv k σ)
        (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl)

def affineLocalToConeLocal : Localization.AtPrime P →+*
    Localization.AtPrime (conePrime k σ P) :=
  (conePrimeLocalizationEquiv k σ P).symm.toRingHom.comp
    (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))

@[instance_reducible] def affineLocalConeAlgebra :
    Algebra (Localization.AtPrime P) (Localization.AtPrime (conePrime k σ P)) :=
  (affineLocalToConeLocal k σ P).toAlgebra

theorem affineLocalToConeLocal_map_maximalIdeal :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (affineLocalToConeLocal k σ P) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (conePrime k σ P)) := by
  rw [affineLocalToConeLocal, ← Ideal.map_map,
    laurentLocal_maximalIdeal_map_eq (AffineRing k σ) P]
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (conePrimeLocalizationEquiv k σ P).symm.toRingHom
    (conePrimeLocalizationEquiv k σ P).symm.surjective

theorem affineLocalToConeLocal_flat :
    letI := affineLocalConeAlgebra k σ P
    Module.Flat (Localization.AtPrime P) (Localization.AtPrime (conePrime k σ P)) := by
  let := affineLocalConeAlgebra k σ P
  let e : Localization.AtPrime (conePrime k σ P) ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime (laurentPrime (AffineRing k σ) P) :=
    { conePrimeLocalizationEquiv k σ P with
      commutes' := by
        intro a
        change conePrimeLocalizationEquiv k σ P
          ((conePrimeLocalizationEquiv k σ P).symm (algebraMap _ _ a)) = _
        exact (conePrimeLocalizationEquiv k σ P).apply_symm_apply _ }
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

theorem coneLocal_quotient_length
    (I : Ideal (Localization.AtPrime P))
    (hI : IsFiniteLength (Localization.AtPrime P) (Localization.AtPrime P ⧸ I)) :
    Module.length (Localization.AtPrime (conePrime k σ P))
      (Localization.AtPrime (conePrime k σ P) ⧸ I.map (affineLocalToConeLocal k σ P)) =
    Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ I) := by
  let := affineLocalConeAlgebra k σ P
  let := affineLocalToConeLocal_flat k σ P
  exact WeightedTorusJets.W25.length_quotient_map_of_flat_local
    (affineLocalToConeLocal_map_maximalIdeal k σ P) I hI

end W17.ConeLocalLength

end

end SiegelZeros

end OAI
