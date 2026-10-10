import OAI.NumberTheory.DirichletL.PrimeRows.Euler
import OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open ProbePhysical

def momentData (η : Character) : RowData where
  η := η
  m := rowMaskElement
  f := 1
  m_ne_zero := rowMaskElement_ne_zero
  f_ne_zero := one_ne_zero
  lambda_dvd := dvd_mul_left _ _
  two_dvd := dvd_mul_right _ _

def momentElement (u : FreeRow) : NonzeroElement := ⟨u.val,u.property.1⟩

theorem momentData_coeff (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData η).character (momentElement u)) I=
      idealCoeff η I*idealRowHom (rowMaskElement^6*u.val) I := by
  simpa only [momentData,momentElement,one_pow,mul_one] using
    idealCoeff_eq_row η ((momentData η).character (momentElement u)) rowMaskElement 1 u.val
      ((momentData η).character_spec (momentElement u)) I

theorem momentData_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : PrimeIdeal) (hP : P.val∉S) :
    idealCoeff ((momentData η).character (momentElement u)) P.val=
      idealCoeff η P.val*idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [momentData_coeff,idealRowHom_argument_mul,
    idealRowHom_prime_sixth_mask rowMaskElement P.val hg,ite_eq_left hc,one_mul]

theorem numerator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) I := by
  have he : idealCoeff (rowCharacter S hS u)=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=_
    rw [excludedTarget_prime]
    by_cases hP : P.val∈S
    · rw [ite_eq_left hP,momentData_coeff,fixedSourcePrincipal_prime,ite_eq_left hP,zero_mul]
    · rw [ite_eq_right hP,rawRow_prime_outside S hS hbad u P hP,
        momentData_prime_outside S hS hbad _ u P hP,
        fixedSourcePrincipal_prime,ite_eq_right hP,one_mul]
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem denominator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((targetRow η u).excludePrimes S hS) I=
      conj (idealCoeff ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) I) := by
  have he : idealCoeff ((targetRow η u).excludePrimes S hS)=
      idealCoeff (((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)).inverse) := by
    apply hom_eq_of_primes
    intro P
    rw [idealCoeff_inverse_conj]
    change idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=_
    rw [target_inverseRow_coeff S hS hbad]
    by_cases hP : P.val∈S
    · rw [ite_eq_left hP,momentData_coeff,excludedTarget_prime,ite_eq_left hP,zero_mul,map_zero]
    · rw [ite_eq_right hP,momentData_prime_outside S hS hbad _ u P hP,
        excludedTarget_prime,ite_eq_right hP,idealCoeff_inverse_conj,map_mul]
      simp only [starRingEnd_self_apply]
  simpa only [idealCoeff_inverse_conj] using congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem numerator_moment_polynomial (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    HeckeDyadic.polynomial (rowCharacter S hS u) inv W D σ freq=
      HeckeDyadic.polynomial ((momentData (fixedSourcePrincipal S hS)).character
        (momentElement u)) inv W D σ freq :=
  HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff _ _
    (numerator_moment_coeff S hS hbad u) inv W D σ freq

theorem denominator_moment_norm (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖HeckeDyadic.polynomial ((targetRow η u).excludePrimes S hS) inv W D σ freq‖=
      ‖HeckeDyadic.polynomial ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) inv (fun x=>conj (W x)) D σ (-freq)‖ :=
  HeckeDetectorCoefficientTransfer.norm_of_oriented_coefficients _ _ true
    (denominator_moment_coeff S hS hbad η u) inv W D σ freq hD

end SevenEighths.ProbeHighRowFamily

end

end OAI
