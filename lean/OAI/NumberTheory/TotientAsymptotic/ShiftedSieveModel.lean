import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveRoots
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.Selberg

namespace OAI

/-! The concrete two-linear-form sieve used for shifted primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def shiftedSievePolynomial (b q : ℕ) : ℕ := q*(b*q+1)

lemma shiftedSievePolynomial_strictMono (b : ℕ) : StrictMono (shiftedSievePolynomial b) := by
  intro q r hqr
  have hsq := Nat.mul_le_mul hqr.le hqr.le
  have hh := Nat.mul_le_mul_left b hsq
  dsimp [shiftedSievePolynomial]
  nlinarith

def oddSievePrimes (z : ℕ) : Finset ℕ :=
  (Nat.primesLE z).filter (fun p => p ≠ 2)

lemma mem_oddSievePrimes {z p : ℕ} : p ∈ oddSievePrimes z ↔ p ≤ z ∧ p.Prime ∧ p ≠ 2 := by
  simp [oddSievePrimes,Nat.mem_primesLE,and_assoc]

lemma oddSievePrimes_prod_squarefree (z : ℕ) : Squarefree (∏ p ∈ oddSievePrimes z,p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    have hpp := (mem_oddSievePrimes.mp hp).2.1
    have hqp := (mem_oddSievePrimes.mp hq).2.1
    exact hpp.coprime_iff_not_dvd.mpr (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp hd))
  · intro p hp
    exact (mem_oddSievePrimes.mp hp).2.1.squarefree

lemma mem_oddSievePrimes_of_dvd {z p : ℕ} (hp : p.Prime)
    (hd : p ∣ ∏ q ∈ oddSievePrimes z,q) : p ∈ oddSievePrimes z := by
  obtain ⟨q,hq,hdq⟩ := hp.prime.exists_mem_finset_dvd hd
  have he := (Nat.prime_dvd_prime_iff_eq hp (mem_oddSievePrimes.mp hq).2.1).mp hdq
  simpa only [he] using hq

def shiftedSieveDensity (b : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => if p ∣ b then (p:ℝ)⁻¹ else 2/(p:ℝ))

lemma shiftedSieveDensity_prime (b p : ℕ) (hp : p.Prime) :
    shiftedSieveDensity b p = if p ∣ b then (p:ℝ)⁻¹ else 2/(p:ℝ) := by
  simp [shiftedSieveDensity,ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

lemma shiftedSieveDensity_positive (b p : ℕ) (hp : p.Prime) : 0 < shiftedSieveDensity b p := by
  rw [shiftedSieveDensity_prime b p hp]
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  split_ifs <;> positivity

lemma shiftedSieveDensity_lt_one (b p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    shiftedSieveDensity b p < 1 := by
  rw [shiftedSieveDensity_prime b p hp]
  have hpR : (2:ℝ)<p := by exact_mod_cast (show 2<p by have := hp.two_le; omega)
  split_ifs
  · exact inv_lt_one_of_one_lt₀ (by linarith)
  · exact (div_lt_one (by linarith)).mpr hpR

/-- Every density and support here is concrete; only the local discrepancy and
bounding sum remain to be estimated in the subsequent counting argument. -/
def shiftedPrimeSieve (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := (Finset.Icc 1 X).image (shiftedSievePolynomial b)
  prodPrimes := ∏ p ∈ oddSievePrimes z,p
  prodPrimes_squarefree := oddSievePrimes_prod_squarefree z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := shiftedSieveDensity b
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => shiftedSieveDensity_positive b p hp
  nu_lt_one_of_prime := fun p hp hd => shiftedSieveDensity_lt_one b p hp
    (mem_oddSievePrimes.mp (mem_oddSievePrimes_of_dvd hp hd)).2.2
  level := y
  one_le_level := hy

end TotientAsymptotic

end

end OAI
