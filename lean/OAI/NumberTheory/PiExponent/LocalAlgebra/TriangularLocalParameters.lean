import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Regular.RegularSequence
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

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
  let e := PiExponentSiegel.W08.coordinateCoefficientSplit (K := K) n
  let q := m.comap e.symm.toRingEquiv.toRingHom
  let : q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have he : e.symm.toRingEquiv.toRingHom.comp MvPolynomial.C =
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)))).toRingHom := by
    apply RingHom.ext
    intro f
    change e.symm (MvPolynomial.C f) =
      Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) f
    apply e.symm_apply_eq.mpr
    exact (PiExponentSiegel.W08.coordinateCoefficientSplit_aeval n f).symm
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
    PiExponentSiegel.W08.coordinateMinpolyIdeal n (firstCoordinatePolynomial K n m) ≤ m :=
  PiExponentSiegel.W08.coordinateMinpolyIdeal_le_of_mem_contraction n
    (firstCoordinatePolynomial K n m) m (firstCoordinatePolynomial_mem K n m)

theorem firstCoordinateRelation_ne_zero :
    Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)
      (firstCoordinatePolynomial K n m) ≠ 0 := by
  intro h
  have h' := congrArg (PiExponentSiegel.W08.coordinateCoefficientSplit (K := K) n) h
  rw [PiExponentSiegel.W08.coordinateCoefficientSplit_aeval, map_zero] at h'
  apply (firstCoordinatePolynomial_irreducible K n m).ne_zero
  simpa using h'

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI
