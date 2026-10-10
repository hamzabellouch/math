import OAI.NumberTheory.TotientAsymptotic.CommonLargestPrime
import Mathlib.Algebra.BigOperators.Associated

namespace OAI

/-! The two cross-prime removals in the unequal-largest-prime case. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma other_prime_dvd_divideFactor {k : ℕ} (i j : Fin k) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (f : Fin k → ℕ)
    (hpi : p ∣ f i) (hqj : q ∣ f j) : q ∣ divideFactor i p f j := by
  by_cases hji : j=i
  · subst j
    have he := Nat.mul_div_cancel' hpi
    have hd : q ∣ p*(f i/p) := by rw [he]; exact hqj
    have hqp : ¬q ∣ p := by
      intro h
      exact hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
    simpa only [divideFactor,Function.update_self] using (hq.dvd_mul.mp hd).resolve_left hqp
  · simpa only [divideFactor,Function.update_of_ne hji] using hqj

def doubleDivide {k : ℕ} (i j : Fin k) (p q : ℕ) (f : Fin k → ℕ) : Fin k → ℕ :=
  divideFactor j q (divideFactor i p f)

def doubleMultiply {k : ℕ} (i j : Fin k) (p q : ℕ) (f : Fin k → ℕ) : Fin k → ℕ :=
  multiplyFactor i p (multiplyFactor j q f)

lemma doubleMultiply_doubleDivide {k : ℕ} (i j : Fin k) (p q : ℕ) (f : Fin k → ℕ)
    (hp : p ∣ f i) (hq : q ∣ divideFactor i p f j) :
    doubleMultiply i j p q (doubleDivide i j p q f)=f := by
  simp only [doubleMultiply,doubleDivide,multiply_divideFactor j q _ hq,
    multiply_divideFactor i p f hp]

lemma prod_doubleDivide {k : ℕ} (i j : Fin k) (p q : ℕ) (f : Fin k → ℕ)
    (hp : p ∣ f i) (hq : q ∣ divideFactor i p f j) :
    (p*q)*(∏ t,doubleDivide i j p q f t)=∏ t,f t := by
  rw [mul_assoc,show q*(∏ t,doubleDivide i j p q f t)=∏ t,divideFactor i p f t from
    prod_divideFactor j q _ hq,prod_divideFactor i p f hp]

lemma doubleDivide_prod_dvd {k : ℕ} (i j : Fin k) (p q : ℕ) (f : Fin k → ℕ)
    (hp : p ∣ f i) (hq : q ∣ divideFactor i p f j) :
    (∏ t,doubleDivide i j p q f t) ∣ ∏ t,f t :=
  ⟨p*q,by rw [mul_comm,prod_doubleDivide i j p q f hp hq]⟩

lemma doubleDivide_prod_pos {k : ℕ} (i j : Fin k) (p q : ℕ) (f : Fin k → ℕ)
    (hp : p ∣ f i) (hq : q ∣ divideFactor i p f j) (hf : 0 < ∏ t,f t) :
    0 < ∏ t,doubleDivide i j p q f t :=
  divideFactor_prod_pos j q _ hq (divideFactor_prod_pos i p f hp hf)

lemma distinct_largest_cross_slots {k : ℕ} (i : Fin k) (f : PairedFactors k)
    (he : pairedProduct f=∏ j,f.2 j) (hl : 2 ≤ f.1 i) (hr : 2 ≤ f.2 i)
    (hlt : largestPrimeFactor (f.2 i) < largestPrimeFactor (f.1 i)) :
    ∃ j l : Fin k,l ≠ i ∧
      largestPrimeFactor (f.2 i) ∣ divideFactor i (largestPrimeFactor (f.1 i)) f.1 j ∧
      largestPrimeFactor (f.1 i) ∣ divideFactor i (largestPrimeFactor (f.2 i)) f.2 l := by
  let p := largestPrimeFactor (f.1 i)
  let q := largestPrimeFactor (f.2 i)
  have hpm := largestPrimeFactor_mem hl
  have hqm := largestPrimeFactor_mem hr
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
  have hpi : p ∣ f.1 i := Nat.dvd_of_mem_primeFactors hpm
  have hqi : q ∣ f.2 i := Nat.dvd_of_mem_primeFactors hqm
  have hpq : p ≠ q := (Nat.ne_of_lt hlt).symm
  have hqp : q ≠ p := hpq.symm
  have hpleft : p ∣ pairedProduct f := hpi.trans (Finset.dvd_prod_of_mem f.1 (Finset.mem_univ i))
  have hqright : q ∣ ∏ j,f.2 j := hqi.trans (Finset.dvd_prod_of_mem f.2 (Finset.mem_univ i))
  have hqleft : q ∣ ∏ j,f.1 j := by rw [← he] at hqright; exact hqright
  have hpright : p ∣ ∏ j,f.2 j := by rw [← he]; exact hpleft
  obtain ⟨j,_,hqj⟩ := (hq.prime.dvd_finsetProd_iff f.1).mp hqleft
  obtain ⟨l,_,hpl⟩ := (hp.prime.dvd_finsetProd_iff f.2).mp hpright
  have hli : l ≠ i := by
    intro hh
    subst l
    have hm := (Nat.mem_primeFactorsList_iff_dvd (by omega : f.2 i ≠ 0) hp).mpr hpl
    have hb := primeFactor_le_largest hm
    exact (not_le_of_gt hlt) hb
  exact ⟨j,l,hli,other_prime_dvd_divideFactor i j hp hq hpq f.1 hpi hqj,
    other_prime_dvd_divideFactor i l hq hp hqp f.2 hqi hpl⟩

end TotientAsymptotic

end

end OAI
