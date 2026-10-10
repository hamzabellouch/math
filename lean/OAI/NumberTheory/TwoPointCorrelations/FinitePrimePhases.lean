import OAI.NumberTheory.TwoPointCorrelations.ShortSumSampling

namespace OAI

/-! The Fourier twists used in qualitative analytic centering count distinct
prime divisors, rather than their multiplicities. Their multiplicativity is
therefore asserted only for coprime arguments. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def finitePrimeDivisorCount (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ p ∈ P, if p ∣ n then 1 else 0

lemma finitePrimeDivisorCount_mul (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (m n : ℕ) (hcop : m.Coprime n) :
    finitePrimeDivisorCount P (m * n) =
      finitePrimeDivisorCount P m + finitePrimeDivisorCount P n := by
  unfold finitePrimeDivisorCount
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hprime := hP p hp
  have hboth : ¬(p ∣ m ∧ p ∣ n) := by
    rintro ⟨hm, hn⟩
    exact hprime.ne_one (Nat.eq_one_of_dvd_coprimes hcop hm hn)
  simp only [hprime.dvd_mul]
  by_cases hm : p ∣ m <;> by_cases hn : p ∣ n <;> simp_all

lemma finitePrimeDivisorCount_prime_outside (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {p : ℕ} (hp : Nat.Prime p) (hout : p ∉ P) :
    finitePrimeDivisorCount P p = 0 := by
  apply sum_eq_zero
  intro q hq
  have hnot : ¬q ∣ p := by
    intro hdiv
    have heq : p = q := (hp.dvd_iff_eq (hP q hq).ne_one).mp hdiv
    exact hout (heq.symm ▸ hq)
  exact ite_eq_right hnot

noncomputable def finitePrimePhase (P : Finset ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  additiveCharacter t (finitePrimeDivisorCount P n)

lemma norm_finitePrimePhase (P : Finset ℕ) (t : ℝ) (n : ℕ) :
    ‖finitePrimePhase P t n‖ = 1 := norm_additiveCharacter _ _

lemma finitePrimePhase_mul (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (t : ℝ) (m n : ℕ) (hcop : m.Coprime n) :
    finitePrimePhase P t (m * n) = finitePrimePhase P t m * finitePrimePhase P t n := by
  unfold finitePrimePhase
  rw [finitePrimeDivisorCount_mul P hP m n hcop, additiveCharacter_nat_add]

noncomputable def twistByPrimePhase (f : ℕ → ℂ) (P : Finset ℕ) (t : ℝ)
    (n : ℕ) : ℂ := f n * finitePrimePhase P t n

lemma Multiplicative.twistByPrimePhase {f : ℕ → ℂ} (hf : Multiplicative f)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (t : ℝ) :
    Multiplicative (TwoPointCorrelations.twistByPrimePhase f P t) := by
  intro m n hm hn hcop
  unfold TwoPointCorrelations.twistByPrimePhase
  rw [hf m n hm hn hcop, finitePrimePhase_mul P hP t m n hcop]
  ring

lemma OneBounded.twistByPrimePhase {f : ℕ → ℂ} (hf : OneBounded f)
    (P : Finset ℕ) (t : ℝ) : OneBounded (TwoPointCorrelations.twistByPrimePhase f P t) := by
  intro n hn
  simpa only [TwoPointCorrelations.twistByPrimePhase, norm_mul,
    norm_finitePrimePhase, mul_one] using hf n hn

lemma twistByPrimePhase_prime_outside (f : ℕ → ℂ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (t : ℝ) {p : ℕ}
    (hp : Nat.Prime p) (hout : p ∉ P) :
    twistByPrimePhase f P t p = f p := by
  simp [twistByPrimePhase, finitePrimePhase,
    finitePrimeDivisorCount_prime_outside P hP hp hout, additiveCharacter]

end TwoPointCorrelations

end OAI
