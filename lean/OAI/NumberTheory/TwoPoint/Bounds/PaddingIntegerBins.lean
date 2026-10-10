import OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding
import OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift

namespace OAI

/-! The squarefree divisor formula uses literal divisibility by the site,
including the site zero. Bin membership is exactly the half-open interval
condition in the manuscript. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma paddingSelectedDivisor_dvd_iff (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) (n : ℤ) :
    (paddingSelectedDivisor Q b : ℤ) ∣ n ↔
      ∀ p : Q, b p = true → (p.val : ℤ) ∣ n := by
  rw [paddingSelectedDivisor, Nat.cast_prod]
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun q : Q => (q.val : ℤ))
      (mem_filter.mpr ⟨mem_univ p, hp⟩)).trans h
  · intro h
    apply prod_dvd_of_coprime
    · intro p _ q _ hpq
      apply Nat.Coprime.cast
      apply (Nat.coprime_primes (hQ p p.property) (hQ q q.property)).mpr
      exact fun he => hpq (Subtype.ext he)
    · intro p hp
      exact h p (mem_filter.mp hp).2

lemma padding_literal_support_iff_dvd (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (n : ℤ) (q : ℕ) (hq : q ∈ retainedPrimeDivisors Q) :
    q.primeFactors ⊆ paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n)) ↔
      (q : ℤ) ∣ n := by
  obtain ⟨b, rfl⟩ := exists_paddingSelection Q q hq
  rw [← padding_supported_iff_primeFactors_subset Q hQ,
    paddingSelectedDivisor_dvd_iff Q hQ b n]
  simp only [PaddingSelectionSupported, decide_eq_true_eq]

lemma paddingBin_eq_iff (η c x : ℝ) (j : ℤ) (hη : 0 < η) :
    paddingBin η c x = j ↔ (j : ℝ) * η ≤ x + c ∧ x + c < ((j : ℝ) + 1) * η := by
  rw [paddingBin, Int.floor_eq_iff, le_div_iff₀ hη, div_lt_iff₀ hη]

lemma paddingAvailablePrimes_integer (Q : Finset ℕ) (n : ℤ) :
    paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n)) =
      Q.filter (fun (p : ℕ) => (p : ℤ) ∣ n) := by
  ext p
  constructor
  · intro hp
    have hpQ := paddingAvailablePrimes_subset Q _ hp
    exact mem_filter.mpr ⟨hpQ, by
      simpa using (mem_paddingAvailablePrimes Q _ ⟨p, hpQ⟩).mp hp⟩
  · intro hp
    exact (mem_paddingAvailablePrimes Q _ ⟨p, (mem_filter.mp hp).1⟩).mpr
      (by simpa using (mem_filter.mp hp).2)

noncomputable def integerPaddingBinMass (Q : Finset ℕ) (n : ℤ) (η c : ℝ) (j : ℤ) : ℝ :=
  (5 : ℝ) ^ (-((Q.filter (fun (p : ℕ) => (p : ℤ) ∣ n)).card : ℤ)) *
    ∑ q ∈ retainedPrimeDivisors Q,
      if (q : ℤ) ∣ n ∧ (j : ℝ) * η ≤ Real.log q + c ∧
          Real.log q + c < ((j : ℝ) + 1) * η
      then (4 : ℝ) ^ q.primeFactors.card else 0

lemma literalPaddingBinMass_integer (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (n : ℤ) (η c : ℝ) (j : ℤ) (hη : 0 < η) :
    literalPaddingBinMass Q (fun p => decide ((p.val : ℤ) ∣ n)) η c j =
      integerPaddingBinMass Q n η c j := by
  unfold literalPaddingBinMass integerPaddingBinMass
  rw [paddingAvailablePrimes_integer]
  congr 1
  apply sum_congr rfl
  intro q hq
  rw [← paddingAvailablePrimes_integer Q n]
  simp only [padding_literal_support_iff_dvd Q hQ n q hq,
    paddingBin_eq_iff η c (Real.log q) j hη]

lemma padding_integer_weight_total (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (n : ℤ) :
    (∑ q ∈ retainedPrimeDivisors Q, if (q : ℤ) ∣ n then (4 : ℝ) ^ q.primeFactors.card else 0) =
      (5 : ℝ) ^ (Q.filter (fun (p : ℕ) => (p : ℤ) ∣ n)).card := by
  have hh := padding_divisor_weight_total Q hQ (fun p => decide ((p.val : ℤ) ∣ n))
  rw [paddingTiltWeight_eq_five_pow, ← paddingAvailablePrimes_card,
    paddingAvailablePrimes_integer] at hh
  convert hh using 1
  apply sum_congr rfl
  intro q hq
  have hd := padding_literal_support_iff_dvd Q hQ n q hq
  rw [paddingAvailablePrimes_integer] at hd
  simp only [hd]

end TwoPointCorrelations

end OAI
