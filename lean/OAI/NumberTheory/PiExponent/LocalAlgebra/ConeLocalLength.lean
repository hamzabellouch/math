import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.Basic
import OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

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
    ← Ideal.comap_comap, laurentPrime_eq_map_polynomialPrime,
    show Ideal.comap (algebraMap (Polynomial A) (LaurentPolynomial A))
        ((polynomialPrime A P).map (algebraMap (Polynomial A) (LaurentPolynomial A))) =
        polynomialPrime A P from
      IsLocalization.under_map_of_isPrime_disjoint
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
  PiExponentJets.W25.length_quotient_map_of_flat_local
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

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
