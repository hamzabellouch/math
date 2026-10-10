import OAI.NumberTheory.TotientAsymptotic.TripleSieveCRT
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.Selberg

namespace OAI

/-! Concrete Selberg sieve for q, aq+1 and bq+1. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def tripleSievePrimes (z : ℕ) : Finset ℕ := (Nat.primesLE z).filter (fun p => 3 < p)

lemma mem_tripleSievePrimes {z p : ℕ} :
    p ∈ tripleSievePrimes z ↔ p ≤ z ∧ p.Prime ∧ 3 < p := by
  simp [tripleSievePrimes,Nat.mem_primesLE,and_assoc]

lemma tripleSievePrimes_squarefree (z : ℕ) : Squarefree (∏ p ∈ tripleSievePrimes z,p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    have hpp := (mem_tripleSievePrimes.mp hp).2.1
    have hqp := (mem_tripleSievePrimes.mp hq).2.1
    exact hpp.coprime_iff_not_dvd.mpr (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp hd))
  · intro p hp
    exact (mem_tripleSievePrimes.mp hp).2.1.squarefree

lemma mem_tripleSievePrimes_of_dvd {z p : ℕ} (hp : p.Prime)
    (hd : p ∣ ∏ q ∈ tripleSievePrimes z,q) : p ∈ tripleSievePrimes z := by
  obtain ⟨q,hq,hdq⟩ := hp.prime.exists_mem_finset_dvd hd
  have he := (Nat.prime_dvd_prime_iff_eq hp (mem_tripleSievePrimes.mp hq).2.1).mp hdq
  simpa only [he] using hq

def tripleSieveDensity (a b : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (tripleRootCount p a b:ℝ)/p)

lemma tripleSieveDensity_prime (a b p : ℕ) (hp : p.Prime) :
    tripleSieveDensity a b p = (tripleRootCount p a b:ℝ)/p := by
  simp [tripleSieveDensity,ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors]

lemma tripleSieveDensity_positive (a b p : ℕ) (hp : p.Prime) :
    0 < tripleSieveDensity a b p := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [tripleSieveDensity_prime a b p hp,tripleRootCount_eq_card]
  have hc : 0 < (tripleSieveRoots p a b).card :=
    Finset.card_pos.mpr ⟨0,zero_mem_tripleSieveRoots p a b⟩
  exact div_pos (by exact_mod_cast hc) (by exact_mod_cast hp.pos)

lemma tripleSieveDensity_lt_one (a b p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    tripleSieveDensity a b p < 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [tripleSieveDensity_prime a b p hp,tripleRootCount_eq_card]
  apply (div_lt_one (by exact_mod_cast hp.pos)).mpr
  exact_mod_cast (tripleSieveRoots_card_le p a b).trans_lt hp3

lemma tripleSievePolynomial_strictMono (a b : ℕ) : StrictMono (tripleSievePolynomial a b) := by
  intro q r hqr
  have ha : a*q+1 ≤ a*r+1 := Nat.add_le_add_right (Nat.mul_le_mul_left a hqr.le) 1
  have hb : b*q+1 ≤ b*r+1 := Nat.add_le_add_right (Nat.mul_le_mul_left b hqr.le) 1
  have hp : 0 < (a*r+1)*(b*r+1) := Nat.mul_pos (by omega) (by omega)
  calc
    tripleSievePolynomial a b q = q*((a*q+1)*(b*q+1)) := by unfold tripleSievePolynomial; ring
    _ ≤ q*((a*r+1)*(b*r+1)) := Nat.mul_le_mul_left q (Nat.mul_le_mul ha hb)
    _ < r*((a*r+1)*(b*r+1)) := Nat.mul_lt_mul_of_pos_right hqr hp
    _ = tripleSievePolynomial a b r := by unfold tripleSievePolynomial; ring

def triplePrimeSieve (a b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := (Finset.Icc 1 X).image (tripleSievePolynomial a b)
  prodPrimes := ∏ p ∈ tripleSievePrimes z,p
  prodPrimes_squarefree := tripleSievePrimes_squarefree z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := tripleSieveDensity a b
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => tripleSieveDensity_positive a b p hp
  nu_lt_one_of_prime := fun p hp hd => tripleSieveDensity_lt_one a b p hp
    (mem_tripleSievePrimes.mp (mem_tripleSievePrimes_of_dvd hp hd)).2.2
  level := y
  one_le_level := hy

end TotientAsymptotic

end

end OAI
