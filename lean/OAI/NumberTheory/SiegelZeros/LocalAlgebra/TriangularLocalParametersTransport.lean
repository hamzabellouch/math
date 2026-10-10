import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Regular.RegularSequence
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ConePrimeLocalization

namespace OAI


namespace SiegelZeros.W08

open Polynomial

variable {K : Type*} [Field K]

noncomputable def coordinatePolynomialSplit (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
  MvPolynomial.finSuccEquiv K n

noncomputable def coordinateCoefficientSplit (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin n) K[X] :=
  (MvPolynomial.renameEquiv K (_root_.finSuccEquiv n)).trans
    (MvPolynomial.optionEquivRight K (Fin n))

@[simp] theorem coordinateCoefficientSplit_X_zero (n : ℕ) :
    coordinateCoefficientSplit (K := K) n (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
  simp [coordinateCoefficientSplit]

@[simp] theorem coordinateCoefficientSplit_X_succ (n : ℕ) (i : Fin n) :
    coordinateCoefficientSplit (K := K) n (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [coordinateCoefficientSplit]

@[simp] theorem coordinateCoefficientSplit_C (n : ℕ) (a : K) :
    coordinateCoefficientSplit n (MvPolynomial.C a) = MvPolynomial.C (Polynomial.C a) := by
  simp [coordinateCoefficientSplit]

theorem coordinateCoefficientSplit_aeval (n : ℕ) (f : K[X]) :
    coordinateCoefficientSplit n (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) f) =
      MvPolynomial.C f := by
  have h : (coordinateCoefficientSplit (K := K) n).toAlgHom.comp
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1)))) =
      IsScalarTower.toAlgHom K K[X] (MvPolynomial (Fin n) K[X]) := by
    apply Polynomial.algHom_ext
    change coordinateCoefficientSplit n
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) Polynomial.X) =
      MvPolynomial.C Polynomial.X
    rw [Polynomial.aeval_X, coordinateCoefficientSplit_X_zero]
  exact AlgHom.congr_fun h f

noncomputable def coordinateMinpolyIdeal (n : ℕ) (f : K[X]) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) f}

theorem coordinateMinpolyIdeal_map (n : ℕ) (f : K[X]) :
    (coordinateMinpolyIdeal n f).map (coordinateCoefficientSplit n).toRingEquiv.toRingHom =
      (Ideal.span {f}).map (MvPolynomial.C : K[X] →+* MvPolynomial (Fin n) K[X]) := by
  simp only [coordinateMinpolyIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  exact congrArg Set.singleton (coordinateCoefficientSplit_aeval n f)

noncomputable def coefficientAdjoinRootQuotientEquiv (n : ℕ) (f : K[X]) :
    (MvPolynomial (Fin n) K[X] ⧸
      (Ideal.span {f}).map (MvPolynomial.C : K[X] →+* MvPolynomial (Fin n) K[X])) ≃ₐ[K]
      MvPolynomial (Fin n) (AdjoinRoot f) :=
  ((MvPolynomial.quotientEquivQuotientMvPolynomial
    (σ := Fin n) (Ideal.span {f} : Ideal K[X])).symm).restrictScalars K

@[simp] theorem coefficientAdjoinRootQuotientEquiv_mk (n : ℕ) (f : K[X])
    (p : MvPolynomial (Fin n) K[X]) :
    coefficientAdjoinRootQuotientEquiv n f (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (AdjoinRoot.mk f) p := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
  rfl

noncomputable def coordinateMinpolyQuotientEquiv (n : ℕ) (f : K[X]) :
    (MvPolynomial (Fin (n + 1)) K ⧸ coordinateMinpolyIdeal n f) ≃ₐ[K]
      MvPolynomial (Fin n) (AdjoinRoot f) :=
  (Ideal.quotientEquivAlg (coordinateMinpolyIdeal n f) _
    (coordinateCoefficientSplit n) (coordinateMinpolyIdeal_map n f).symm).trans
      (coefficientAdjoinRootQuotientEquiv n f)

theorem coordinateMinpolyQuotientEquiv_mk (n : ℕ) (f : K[X])
    (p : MvPolynomial (Fin (n+1)) K) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (AdjoinRoot.mk f) (coordinateCoefficientSplit n p) := by
  exact coefficientAdjoinRootQuotientEquiv_mk n f (coordinateCoefficientSplit n p)

@[simp] theorem coordinateMinpolyQuotientEquiv_X_zero (n : ℕ) (f : K[X]) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ (MvPolynomial.X 0)) =
      MvPolynomial.C (AdjoinRoot.root f) := by
  rw [coordinateMinpolyQuotientEquiv_mk, coordinateCoefficientSplit_X_zero]
  simp

@[simp] theorem coordinateMinpolyQuotientEquiv_X_succ (n : ℕ) (f : K[X]) (i : Fin n) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ (MvPolynomial.X i.succ)) =
      MvPolynomial.X i := by
  rw [coordinateMinpolyQuotientEquiv_mk, coordinateCoefficientSplit_X_succ]
  simp

@[simp] theorem coordinateMinpolyQuotientEquiv_C (n : ℕ) (f : K[X]) (a : K) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      MvPolynomial.C (algebraMap K (AdjoinRoot f) a) := by
  rw [coordinateMinpolyQuotientEquiv_mk, coordinateCoefficientSplit_C]
  simp

theorem coordinateMinpolyIdeal_le_of_mem_contraction (n : ℕ) (f : K[X])
    (m : Ideal (MvPolynomial (Fin (n+1)) K))
    (hf : f ∈ m.comap (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1)))).toRingHom) :
    coordinateMinpolyIdeal n f ≤ m := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact hf

end SiegelZeros.W08


noncomputable section
namespace SiegelZeros.W10.TriangularLocalParameters

open RingTheory.Sequence
open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S]

theorem scalar_top_eq_principal (r : R) :
    r • (⊤ : Ideal R) = Ideal.span {r} := by
  rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]

def principalModuleQuotientEquiv (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) : QuotSMulTop r R ≃+* S :=
  (Ideal.quotEquivOfEq ((scalar_top_eq_principal r).trans hker.symm)).trans
    (RingHom.quotientKerEquivOfSurjective hπ)

@[simp] theorem principalModuleQuotientEquiv_mk (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (hker : RingHom.ker π = Ideal.span {r}) (x : R) :
    principalModuleQuotientEquiv π hπ r hker (Submodule.Quotient.mk x) = π x := by
  change (RingHom.quotientKerEquivOfSurjective hπ)
    ((Ideal.quotEquivOfEq ((scalar_top_eq_principal r).trans hker.symm))
      (Ideal.Quotient.mk (r • (⊤ : Ideal R)) x)) = π x
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem regular_cons_of_principal_kernel (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) (hr : IsSMulRegular R r)
    (xs : List R) (hxs : IsRegular S (xs.map π)) : IsRegular R (r :: xs) := by
  let e := principalModuleQuotientEquiv π hπ r hker
  apply IsRegular.cons hr
  apply (e.toAddEquiv.isRegular_congr ?_).mpr hxs
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a _ z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change e (Submodule.Quotient.mk (a * z)) = π a * e (Submodule.Quotient.mk z)
    calc
      e (Submodule.Quotient.mk (a * z)) = π (a * z) :=
        principalModuleQuotientEquiv_mk π hπ r hker (a * z)
      _ = π a * π z := π.map_mul a z
      _ = π a * e (Submodule.Quotient.mk z) :=
        congrArg (fun y : S => π a * y)
          (principalModuleQuotientEquiv_mk π hπ r hker z).symm

theorem ofList_cons_eq_comap (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) (xs : List R) :
    Ideal.ofList (r :: xs) = Ideal.comap π (Ideal.ofList (xs.map π)) := by
  rw [← Ideal.map_ofList, Ideal.comap_map_of_surjective π hπ, Ideal.ofList_cons]
  change Ideal.span {r} ⊔ Ideal.ofList xs = Ideal.ofList xs ⊔ RingHom.ker π
  rw [hker, sup_comm]

theorem lift_parameters [IsLocalRing R] [IsLocalRing S]
    (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) (hr : IsSMulRegular R r)
    (ys : List S) (hys : IsRegular S ys)
    (hspan : Ideal.ofList ys = IsLocalRing.maximalIdeal S) :
    ∃ xs : List R, xs.length = ys.length + 1 ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R := by
  obtain ⟨xs, hxs⟩ := (List.map_surjective_iff.mpr hπ) ys
  refine ⟨r :: xs, ?_, ?_, ?_⟩
  · simpa using congrArg (fun zs : List S => zs.length + 1) hxs
  · apply regular_cons_of_principal_kernel π hπ r hker hr xs
    simpa [hxs] using hys
  · rw [ofList_cons_eq_comap π hπ r hker xs, hxs, hspan]
    let : IsLocalHom π := IsLocalHom.of_surjective π hπ
    exact IsLocalRing.maximalIdeal_comap π

theorem regular_element_of_ne_zero [IsDomain R] (r : R) (hr : r ≠ 0) : IsSMulRegular R r :=
  fun _ _ h => mul_left_cancel₀ hr h

theorem singleton_parameter_regular [IsDomain R] [IsLocalRing R]
    (r : R) (hr : r ≠ 0) (hspan : Ideal.span {r} = IsLocalRing.maximalIdeal R) :
    IsRegular R [r] := by
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (M := R) ?_).mpr
  · exact (isWeaklyRegular_singleton_iff R r).mpr (regular_element_of_ne_zero r hr)
  · intro a ha
    have har : a = r := by simpa using ha
    subst a
    rw [← hspan]
    exact Ideal.subset_span (by simp)

section OneVariable
variable (K : Type*) [Field K] (m : Ideal (Polynomial K)) [m.IsMaximal]

def firstPolynomial : Polynomial K := Submodule.IsPrincipal.generator m

theorem firstPolynomial_ne_zero : firstPolynomial K m ≠ 0 := by
  apply mt (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero m).mpr
  exact Ring.ne_bot_of_isMaximal_of_not_isField (inferInstance : m.IsMaximal)
    (Polynomial.not_isField K)

def firstLocalParameter : Localization.AtPrime m :=
  algebraMap (Polynomial K) (Localization.AtPrime m) (firstPolynomial K m)

theorem firstLocalParameter_ne_zero : firstLocalParameter K m ≠ 0 := by
  exact (FaithfulSMul.algebraMap_eq_zero_iff (Polynomial K) (Localization.AtPrime m)).not.mpr
    (firstPolynomial_ne_zero K m)

theorem firstLocalParameter_span :
    Ideal.span {firstLocalParameter K m} = IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  calc
    Ideal.span {firstLocalParameter K m} =
        (Ideal.span {Submodule.IsPrincipal.generator m}).map
          (algebraMap (Polynomial K) (Localization.AtPrime m)) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    _ = m.map (algebraMap (Polynomial K) (Localization.AtPrime m)) :=
      congrArg (Ideal.map (algebraMap (Polynomial K) (Localization.AtPrime m)))
        (Ideal.span_singleton_generator m)
    _ = IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
      Localization.AtPrime.map_eq_maximalIdeal

theorem oneVariable_parameters :
    ∃ xs : List (Localization.AtPrime m), xs.length = 1 ∧
      IsRegular (Localization.AtPrime m) xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  refine ⟨[firstLocalParameter K m], rfl, ?_, ?_⟩
  · exact singleton_parameter_regular (firstLocalParameter K m)
      (firstLocalParameter_ne_zero K m) (firstLocalParameter_span K m)
  · rw [Ideal.ofList_singleton]
    exact firstLocalParameter_span K m

end OneVariable

section ZeroVariables
variable (K : Type*) [Field K] (m : Ideal (MvPolynomial (Fin 0) K)) [m.IsMaximal]

theorem zeroVariable_maximal_eq_bot : m = ⊥ := by
  apply le_antisymm
  · intro p hp
    obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (Fin 0) p
    by_cases hc : c = 0
    · simp [hc]
    · have hu : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 0) K) :=
        (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
      exact False.elim ((inferInstance : m.IsMaximal).ne_top (m.eq_top_of_isUnit_mem hp hu))
  · exact bot_le

theorem zeroVariable_parameters :
    ∃ xs : List (Localization.AtPrime m), xs.length = 0 ∧
      IsRegular (Localization.AtPrime m) xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  refine ⟨[], rfl, IsRegular.nil _ _, ?_⟩
  rw [Ideal.ofList_nil, ← Localization.AtPrime.map_eq_maximalIdeal]
  simpa only [Ideal.map_bot] using
    (congrArg (Ideal.map
      (algebraMap (MvPolynomial (Fin 0) K) (Localization.AtPrime m)))
      (zeroVariable_maximal_eq_bot K m)).symm

end ZeroVariables

variable (K : Type*) [Field K] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin (n + 1)) K)) [m.IsMaximal]

theorem maximal_coefficient_contraction {A : Type*} [CommRing A] [IsJacobsonRing A]
    (j : ℕ) (q : Ideal (MvPolynomial (Fin j) A)) [q.IsMaximal] :
    (q.comap (MvPolynomial.C : A →+* MvPolynomial (Fin j) A)).IsMaximal := by
  rw [← @Ideal.mk_ker _ _ q, RingHom.ker_eq_comap_bot, Ideal.comap_comap]
  let := (Ideal.bot_quotient_isMaximal_iff _).mpr (inferInstance : q.IsMaximal)
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    (MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing q) ⊥

def firstCoordinateContraction : Ideal (Polynomial K) :=
  m.comap (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)))).toRingHom

theorem firstCoordinateContraction_isMaximal : (firstCoordinateContraction K n m).IsMaximal := by
  let e := SiegelZeros.W08.coordinateCoefficientSplit (K := K) n
  let q := m.comap e.symm.toRingEquiv.toRingHom
  let : q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have he : e.symm.toRingEquiv.toRingHom.comp MvPolynomial.C =
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)))).toRingHom := by
    apply RingHom.ext
    intro f
    change e.symm (MvPolynomial.C f) =
      Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) f
    apply e.symm_apply_eq.mpr
    exact (SiegelZeros.W08.coordinateCoefficientSplit_aeval n f).symm
  have hq := maximal_coefficient_contraction n q
  simpa only [q, Ideal.comap_comap, he, firstCoordinateContraction] using hq

def firstCoordinatePolynomial : Polynomial K :=
  Submodule.IsPrincipal.generator (firstCoordinateContraction K n m)

theorem firstCoordinatePolynomial_irreducible : Irreducible (firstCoordinatePolynomial K n m) := by
  let := firstCoordinateContraction_isMaximal K n m
  apply (Submodule.IsPrincipal.prime_generator_of_isPrime
    (firstCoordinateContraction K n m) ?_).irreducible
  exact Ring.ne_bot_of_isMaximal_of_not_isField
    (firstCoordinateContraction_isMaximal K n m) (Polynomial.not_isField K)

omit [m.IsMaximal] in
theorem firstCoordinatePolynomial_mem :
    firstCoordinatePolynomial K n m ∈ firstCoordinateContraction K n m :=
  Submodule.IsPrincipal.generator_mem _

omit [m.IsMaximal] in
theorem firstCoordinateIdeal_le :
    SiegelZeros.W08.coordinateMinpolyIdeal n (firstCoordinatePolynomial K n m) ≤ m :=
  SiegelZeros.W08.coordinateMinpolyIdeal_le_of_mem_contraction n
    (firstCoordinatePolynomial K n m) m (firstCoordinatePolynomial_mem K n m)

theorem firstCoordinateRelation_ne_zero :
    Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)
      (firstCoordinatePolynomial K n m) ≠ 0 := by
  intro h
  have h' := congrArg (SiegelZeros.W08.coordinateCoefficientSplit (K := K) n) h
  rw [SiegelZeros.W08.coordinateCoefficientSplit_aeval, map_zero] at h'
  apply (firstCoordinatePolynomial_irreducible K n m).ne_zero
  simpa using h'

end SiegelZeros.W10.TriangularLocalParameters

end

noncomputable section
namespace SiegelZeros.W23

variable {A : Type*} [CommRing A]

def quotientParameterPrime (I m : Ideal A) (_hI : I ≤ m) : Ideal (A ⧸ I) :=
  m.map (Ideal.Quotient.mk I)

instance quotientParameterPrime_isPrime (I m : Ideal A) [m.IsPrime] (hI : I ≤ m) :
    (quotientParameterPrime I m hI).IsPrime :=
  Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk I) (I := m)
    Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hI)

instance quotientParameterPrime_isMaximal (I m : Ideal A) [m.IsMaximal] (hI : I ≤ m) :
    (quotientParameterPrime I m hI).IsMaximal :=
  Ideal.IsMaximal.map_of_surjective_of_ker_le (f := Ideal.Quotient.mk I) (m := m)
    Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hI)

@[simp] theorem mem_quotientParameterPrime_mk (I m : Ideal A) (hI : I ≤ m) (a : A) :
    Ideal.Quotient.mk I a ∈ quotientParameterPrime I m hI ↔ a ∈ m :=
  Ideal.mem_quotient_iff_mem hI

def parameterLocalizedIdeal (I m : Ideal A) [m.IsPrime] :
    Ideal (Localization.AtPrime m) :=
  I.map (algebraMap A (Localization.AtPrime m))

variable (I m : Ideal A) [m.IsPrime] (hI : I ≤ m)

def parameterLocalizationMap :
    Localization.AtPrime m →+* Localization.AtPrime (quotientParameterPrime I m hI) :=
  IsLocalization.map (Localization.AtPrime (quotientParameterPrime I m hI))
    (Ideal.Quotient.mk I) (M := m.primeCompl)
    (S := Localization.AtPrime m)
    (T := (quotientParameterPrime I m hI).primeCompl) (by
      intro a ha
      change Ideal.Quotient.mk I a ∉ quotientParameterPrime I m hI
      exact fun h => ha ((mem_quotientParameterPrime_mk I m hI a).mp h))

@[simp] theorem parameterLocalizationMap_algebraMap (a : A) :
    parameterLocalizationMap I m hI (algebraMap A (Localization.AtPrime m) a) =
      algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI))
        (Ideal.Quotient.mk I a) :=
  IsLocalization.map_eq _ a

theorem parameterLocalizedIdeal_le_ker :
    parameterLocalizedIdeal I m ≤ RingHom.ker (parameterLocalizationMap I m hI) := by
  rw [parameterLocalizedIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  change parameterLocalizationMap I m hI (algebraMap A (Localization.AtPrime m) a) = 0
  rw [parameterLocalizationMap_algebraMap,
    (Ideal.Quotient.eq_zero_iff_mem).mpr ha, map_zero]

def parameterLocalQuotientForward :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) →+*
      Localization.AtPrime (quotientParameterPrime I m hI) :=
  Ideal.Quotient.lift _ (parameterLocalizationMap I m hI)
    (fun x hx => (RingHom.mem_ker (f := parameterLocalizationMap I m hI) (r := x)).mp
      (parameterLocalizedIdeal_le_ker I m hI hx))

@[simp] theorem parameterLocalQuotientForward_mk (x : Localization.AtPrime m) :
    parameterLocalQuotientForward I m hI (Ideal.Quotient.mk _ x) =
      parameterLocalizationMap I m hI x := rfl

def parameterQuotientToLocalQuotient :
    (A ⧸ I) →+* (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (parameterLocalizedIdeal I m)).comp
      (algebraMap A (Localization.AtPrime m)))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))

@[simp] theorem parameterQuotientToLocalQuotient_mk (a : A) :
    parameterQuotientToLocalQuotient I m (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (parameterLocalizedIdeal I m)
        (algebraMap A (Localization.AtPrime m) a) := rfl

theorem parameterQuotientToLocalQuotient_units
    (s : (quotientParameterPrime I m hI).primeCompl) :
    IsUnit (parameterQuotientToLocalQuotient I m (s : A ⧸ I)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
  have ham : a ∉ m := by
    intro ham
    apply s.property
    change (s : A ⧸ I) ∈ m.map (Ideal.Quotient.mk I)
    rw [← ha]
    exact Ideal.mem_map_of_mem _ ham
  rw [← ha, parameterQuotientToLocalQuotient_mk]
  exact (IsLocalization.map_units (Localization.AtPrime m) (⟨a, ham⟩ : m.primeCompl)).map
    (Ideal.Quotient.mk (parameterLocalizedIdeal I m))

def parameterLocalQuotientReverse :
    Localization.AtPrime (quotientParameterPrime I m hI) →+*
      (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  IsLocalization.lift (M := (quotientParameterPrime I m hI).primeCompl)
    (S := Localization.AtPrime (quotientParameterPrime I m hI))
    (parameterQuotientToLocalQuotient_units I m hI)

@[simp] theorem parameterLocalQuotientReverse_algebraMap (x : A ⧸ I) :
    parameterLocalQuotientReverse I m hI
      (algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI)) x) =
      parameterQuotientToLocalQuotient I m x :=
  IsLocalization.lift_eq _ x

theorem parameterLocalQuotient_reverse_forward :
    (parameterLocalQuotientReverse I m hI).comp (parameterLocalQuotientForward I m hI) =
      RingHom.id (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext m.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, parameterLocalQuotientForward_mk,
    parameterLocalizationMap_algebraMap, parameterLocalQuotientReverse_algebraMap,
    parameterQuotientToLocalQuotient_mk]

theorem parameterLocalQuotient_forward_reverse :
    (parameterLocalQuotientForward I m hI).comp (parameterLocalQuotientReverse I m hI) =
      RingHom.id (Localization.AtPrime (quotientParameterPrime I m hI)) := by
  apply IsLocalization.ringHom_ext (quotientParameterPrime I m hI).primeCompl
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, parameterLocalQuotientReverse_algebraMap,
    parameterQuotientToLocalQuotient_mk, parameterLocalQuotientForward_mk,
    parameterLocalizationMap_algebraMap]

def localizationQuotientParametersEquiv :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      Localization.AtPrime (quotientParameterPrime I m hI) where
  toFun := parameterLocalQuotientForward I m hI
  invFun := parameterLocalQuotientReverse I m hI
  left_inv x := RingHom.congr_fun (parameterLocalQuotient_reverse_forward I m hI) x
  right_inv x := RingHom.congr_fun (parameterLocalQuotient_forward_reverse I m hI) x
  map_mul' := (parameterLocalQuotientForward I m hI).map_mul
  map_add' := (parameterLocalQuotientForward I m hI).map_add

@[simp] theorem localizationQuotientParametersEquiv_mk_algebraMap (a : A) :
    localizationQuotientParametersEquiv I m hI
      (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime m) a)) =
    algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI))
      (Ideal.Quotient.mk I a) :=
  parameterLocalizationMap_algebraMap I m hI a

include hI in

theorem parameterLocalQuotient_isLocalRing :
    IsLocalRing (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  (localizationQuotientParametersEquiv I m hI).symm.isLocalRing

theorem localizationQuotientParametersEquiv_maximalIdeal :
    letI := parameterLocalQuotient_isLocalRing I m hI
    (IsLocalRing.maximalIdeal (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m)).map
      (localizationQuotientParametersEquiv I m hI).toRingHom =
      IsLocalRing.maximalIdeal (Localization.AtPrime (quotientParameterPrime I m hI)) := by
  let := parameterLocalQuotient_isLocalRing I m hI
  exact IsLocalRing.map_ringEquiv_maximalIdeal (localizationQuotientParametersEquiv I m hI)

def localizationQuotientParametersResidueEquiv :
    letI := parameterLocalQuotient_isLocalRing I m hI
    IsLocalRing.ResidueField (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime (quotientParameterPrime I m hI)) := by
  letI := parameterLocalQuotient_isLocalRing I m hI
  exact IsLocalRing.ResidueField.mapEquiv (localizationQuotientParametersEquiv I m hI)

theorem localizationQuotientParametersResidueEquiv_residue
    (x : Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :
    letI := parameterLocalQuotient_isLocalRing I m hI
    localizationQuotientParametersResidueEquiv I m hI (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (localizationQuotientParametersEquiv I m hI x) := by
  let := parameterLocalQuotient_isLocalRing I m hI
  let : IsLocalHom (localizationQuotientParametersEquiv I m hI).toRingHom :=
    IsLocalHom.of_surjective (localizationQuotientParametersEquiv I m hI).toRingHom
      (localizationQuotientParametersEquiv I m hI).surjective
  exact IsLocalRing.ResidueField.map_residue
    (localizationQuotientParametersEquiv I m hI).toRingHom x

theorem parameterLocalizedIdeal_span_singleton (x : A) :
    parameterLocalizedIdeal (Ideal.span {x}) m =
      Ideal.span {algebraMap A (Localization.AtPrime m) x} := by
  simp only [parameterLocalizedIdeal, Ideal.map_span, Set.image_singleton]

variable {B : Type*} [CommRing B]

local instance parameterEquivImage_isPrime (e : A ≃+* B) (P : Ideal A) [P.IsPrime] :
    (P.map e.toRingHom).IsPrime :=
  Ideal.map_isPrime_of_equiv e

theorem atPrimeImage_comap (e : A ≃+* B) (P : Ideal A) :
    P = (P.map e.toRingHom).comap e.toRingHom := by
  ext a
  change a ∈ P ↔ e a ∈ P.map e.toRingHom
  exact Ideal.apply_mem_of_equiv_iff.symm

def atPrimeEquivOfRingEquiv (e : A ≃+* B) (P : Ideal A) [P.IsPrime] :
    Localization.AtPrime P ≃+* Localization.AtPrime (P.map e.toRingHom) :=
  WeightedTorusJets.W22.primeLocalizationEquiv e P (P.map e.toRingHom)
    (atPrimeImage_comap e P)

@[simp] theorem atPrimeEquivOfRingEquiv_algebraMap
    (e : A ≃+* B) (P : Ideal A) [P.IsPrime] (a : A) :
    atPrimeEquivOfRingEquiv e P (algebraMap A (Localization.AtPrime P) a) =
      algebraMap B (Localization.AtPrime (P.map e.toRingHom)) (e a) :=
  IsLocalization.ringEquivOfRingEquiv_eq
    (WeightedTorusJets.W22.primeCompl_map_eq_of_comap e P (P.map e.toRingHom)
      (atPrimeImage_comap e P)) a

def localizationQuotientParametersEquivTrans (e : (A ⧸ I) ≃+* B) :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      Localization.AtPrime ((quotientParameterPrime I m hI).map e.toRingHom) :=
  (localizationQuotientParametersEquiv I m hI).trans
    (atPrimeEquivOfRingEquiv e (quotientParameterPrime I m hI))

@[simp] theorem localizationQuotientParametersEquivTrans_mk_algebraMap
    (e : (A ⧸ I) ≃+* B) (a : A) :
    localizationQuotientParametersEquivTrans I m hI e
      (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime m) a)) =
      algebraMap B
        (Localization.AtPrime ((quotientParameterPrime I m hI).map e.toRingHom))
        (e (Ideal.Quotient.mk I a)) := by
  simp only [localizationQuotientParametersEquivTrans, RingEquiv.trans_apply,
    localizationQuotientParametersEquiv_mk_algebraMap, atPrimeEquivOfRingEquiv_algebraMap]


end SiegelZeros.W23


namespace SiegelZeros.W10.TriangularLocalParameters

open RingTheory.Sequence
universe u

theorem polynomialMaximal_regularParameters (n : ℕ) :
    ∀ (K : Type u) [Field K] (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal],
      ∃ xs : List (Localization.AtPrime m), xs.length = n ∧
        IsRegular (Localization.AtPrime m) xs ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  induction n with
  | zero =>
    intro K _ m _
    exact zeroVariable_parameters K m
  | succ n ih =>
    intro K _ m _
    let A := MvPolynomial (Fin (n + 1)) K
    let f : Polynomial K := firstCoordinatePolynomial K n m
    let : Fact (Irreducible f) := ⟨firstCoordinatePolynomial_irreducible K n m⟩
    let I : Ideal A := SiegelZeros.W08.coordinateMinpolyIdeal n f
    have hI : I ≤ m := firstCoordinateIdeal_le K n m
    let e := (SiegelZeros.W08.coordinateMinpolyQuotientEquiv n f).toRingEquiv
    let qm := SiegelZeros.W23.quotientParameterPrime I m hI
    let p : Ideal (MvPolynomial (Fin n) (AdjoinRoot f)) := qm.map e.toRingHom
    let : p.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := e.toRingHom) (m := qm) e.surjective (by simp)
    obtain ⟨ys, hylen, hyreg, hyspan⟩ := ih (AdjoinRoot f) p
    let J : Ideal (Localization.AtPrime m) := SiegelZeros.W23.parameterLocalizedIdeal I m
    let E : (Localization.AtPrime m ⧸ J) ≃+* Localization.AtPrime p :=
      SiegelZeros.W23.localizationQuotientParametersEquivTrans I m hI e
    let π : Localization.AtPrime m →+* Localization.AtPrime p :=
      E.toRingHom.comp (Ideal.Quotient.mk J)
    have hπ : Function.Surjective π := E.surjective.comp Ideal.Quotient.mk_surjective
    let g : A := Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) f
    let r : Localization.AtPrime m := algebraMap A (Localization.AtPrime m) g
    have hg : g ≠ 0 := firstCoordinateRelation_ne_zero K n m
    have hr : r ≠ 0 :=
      (FaithfulSMul.algebraMap_eq_zero_iff A (Localization.AtPrime m)).not.mpr hg
    have hker : RingHom.ker π = Ideal.span {r} := by
      rw [show π = E.toRingHom.comp (Ideal.Quotient.mk J) from rfl,
        RingHom.ker_comp_of_injective _ E.injective, Ideal.mk_ker]
      change (Ideal.span {g}).map (algebraMap A (Localization.AtPrime m)) = Ideal.span {r}
      rw [Ideal.map_span, Set.image_singleton]
    obtain ⟨xs, hxlen, hxreg, hxspan⟩ := lift_parameters π hπ r hker
      (regular_element_of_ne_zero r hr) ys hyreg hyspan
    refine ⟨xs, ?_, hxreg, hxspan⟩
    simpa [hylen] using hxlen

end SiegelZeros.W10.TriangularLocalParameters


namespace SiegelZeros.W23

theorem intrinsic_length_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : R →ₛₗ[e.toRingHom] S :=
    { toFun := e
      map_add' := e.map_add'
      map_smul' := by
        intro r x
        exact e.map_mul' r x }
  exact WeightedTorusJets.W22.length_eq_of_semilinear_bijective
    e.toRingHom f e.bijective

theorem quotient_module_length_eq_intrinsic {R : Type*} [CommRing R] (I : Ideal R) :
    Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) := by
  have hq : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  exact Module.length_eq_of_surjective (M := R ⧸ I) hq

variable {A : Type*} [CommRing A] (I P : Ideal A) [P.IsPrime] (hI : I ≤ P)

theorem parameterLocalizationMap_surjective :
    Function.Surjective (parameterLocalizationMap I P hI) := by
  intro y
  obtain ⟨x, hx⟩ := (localizationQuotientParametersEquiv I P hI).surjective y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨z, hx⟩

theorem quotient_localized_length_eq :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) =
    Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
      (Localization.AtPrime (quotientParameterPrime I P hI)) := by
  calc
    Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) =
      Module.length (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P)
        (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) :=
      quotient_module_length_eq_intrinsic (parameterLocalizedIdeal I P)
    _ = Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
        (Localization.AtPrime (quotientParameterPrime I P hI)) :=
      intrinsic_length_eq_of_ringEquiv (localizationQuotientParametersEquiv I P hI)

theorem quotient_localized_length_eq_explicit :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap A (Localization.AtPrime P))) =
    Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
      (Localization.AtPrime (quotientParameterPrime I P hI)) :=
  quotient_localized_length_eq I P hI

end SiegelZeros.W23


namespace SiegelZeros.W10.TriangularLocalParameters

open RingTheory.Sequence

variable {R S : Type*} [CommRing R] [CommRing S]

theorem regular_map_ringEquiv (e : R ≃+* S) (xs : List R)
    (hxs : IsRegular R xs) : IsRegular S (xs.map e.toRingHom) := by
  apply (e.toAddEquiv.isRegular_congr ?_).mp hxs
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a _ z
  exact e.map_mul a z

theorem regularParameters_transport [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (n : ℕ)
    (h : ∃ xs : List R, xs.length = n ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R) :
    ∃ ys : List S, ys.length = n ∧ IsRegular S ys ∧
      Ideal.ofList ys = IsLocalRing.maximalIdeal S := by
  obtain ⟨xs, hlen, hreg, hspan⟩ := h
  refine ⟨xs.map e.toRingHom, ?_, regular_map_ringEquiv e xs hreg, ?_⟩
  · simpa using hlen
  · rw [← Ideal.map_ofList, hspan]
    exact IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective

theorem polynomialMaximal_regularParameters_of_ringEquiv (n : ℕ) (K : Type*) [Field K]
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal]
    [IsLocalRing R] (e : R ≃+* Localization.AtPrime m) :
    ∃ xs : List R, xs.length = n ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R :=
  regularParameters_transport e.symm n (polynomialMaximal_regularParameters n K m)

end SiegelZeros.W10.TriangularLocalParameters

end

end OAI
