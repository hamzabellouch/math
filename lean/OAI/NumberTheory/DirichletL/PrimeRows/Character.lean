import OAI.NumberTheory.DirichletL.PrimeRows.Valuation
import OAI.NumberTheory.DirichletL.Detector.FixedEuler
import OAI.NumberTheory.DirichletL.Hecke.RowClosure
import OAI.NumberTheory.DirichletL.Hecke.Conjugation

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve ProbePhysical
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def rowMaskElement : O := 2*λ₀

theorem rowMaskElement_ne_zero : rowMaskElement≠0 :=
  mul_ne_zero (by norm_num) PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero

def rawRow (u : FreeRow) : Character := Classical.choose
  (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))

theorem rawRow_coeff (u : FreeRow) (I : Ideal O) :
    idealCoeff (rawRow u) I=idealCoeff (fixedSourcePrincipal ∅ (by simp)) I*
      idealRowHom (rowMaskElement^6*u.val) I := by
  have he := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2
  simpa only [one_pow,mul_one] using idealCoeff_eq_row _ (rawRow u) rowMaskElement 1 u.val he I

theorem outside_good_coprime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (P : PrimeIdeal) (hP : P.val∉S) :
    λ₀∉P.val ∧ IsCoprime P.val (Ideal.span {rowMaskElement}) := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have hn : P.val∉fixedBadPrimes := fun hh => hP (hbad hh)
  have hg := (prime_good_iff_not_bad P.val).mpr hn
  refine ⟨hg.1,?_⟩
  have hc := (prime_coprime_fixedProduct S hS P).mpr hP
  rw [IsCoprime.prod_right_iff] at hc
  have hLam : Ideal.span {λ₀}∈S := hbad (Finset.mem_insert_self _ _)
  have h2 : Ideal.span {(2 : O)}∈S := hbad (by simp [fixedBadPrimes])
  unfold rowMaskElement
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact (hc _ h2).mul_right (hc _ hLam)

theorem rawRow_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (P : PrimeIdeal) (hP : P.val∉S) :
    idealCoeff (rawRow u) P.val=idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [rawRow_coeff,fixedSourcePrincipal_prime]
  rw [ite_eq_right (by simp),one_mul]
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask rowMaskElement P.val hg,
    ite_eq_left hc,one_mul]

def rowCharacter (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Character :=
  (rawRow u).excludePrimes S hS

def sourceRowCoeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Ideal O→*₀ℂ where
  toFun I := highExclusion S hS I*idealRowHom u.val I
  map_zero' := by rw [(idealRowHom u.val).map_zero, mul_zero]
  map_one' := by rw [map_one,map_one,mul_one]
  map_mul' I J := by simp only [map_mul]; ring

theorem hom_eq_of_primes (f g : Ideal O→*₀ℂ) (h : ∀P : PrimeIdeal,f P.val=g P.val) : f=g := by
  ext I
  by_cases hI : I=0
  · subst I; rw [map_zero,map_zero]
  have hf := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq f)
  have hg := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq g)
  rw [←hf,←hg]
  change (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map f).prod)=
    (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map g).prod)
  rw [ite_eq_right hI,ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  exact h ⟨P,UniqueFactorizationMonoid.prime_of_normalized_factor P hP⟩

theorem rowCharacter_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=highExclusion S hS I*idealRowHom u.val I := by
  have he : idealCoeff (rowCharacter S hS u)=sourceRowCoeff S hS u := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=
      highExclusion S hS P.val*idealRowHom u.val P.val
    rw [excludedTarget_prime,highExclusion_prime]
    by_cases hP : P.val∈S
    · simp only [ite_eq_left hP,zero_mul]
    · simp only [ite_eq_right hP,one_mul]
      exact rawRow_prime_outside S hS hbad u P hP
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem target_inverseRow_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (P : PrimeIdeal) :
    idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=
      if P.val∈S then 0 else idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val) := by
  rw [excludedTarget_prime,idealCoeff_product,idealCoeff_inverse_conj]
  by_cases hP : P.val∈S
  · simp only [ite_eq_left hP]
  · rw [ite_eq_right hP,ite_eq_right hP,rawRow_prime_outside S hS hbad u P hP]

end SevenEighths.ProbeHighRowFamily

end

end OAI
