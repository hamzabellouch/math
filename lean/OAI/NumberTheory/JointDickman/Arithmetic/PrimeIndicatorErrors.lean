import OAI.NumberTheory.JointDickman.Arithmetic.PrimeCountChernoff
import OAI.NumberTheory.JointDickman.Amplification.RegularityChernoffFactors

namespace OAI

/-! # Stable prime-count estimates for the conditional indicator parameters -/

namespace JointDickman

open Finset

/-- Absolute errors in the inclusion probabilities control every restricted mean. -/
theorem restricted_indicator_mean_error (P Q : Finset ℕ) (q : ℕ → ℝ) {D : ℝ}
    (hD : (∑ p ∈ P, |q p - (1 / 2 : ℝ) / p|) ≤ D) :
    |(∑ p ∈ P ∩ Q, q p) - (1 / 2 : ℝ) * (∑ p ∈ P ∩ Q, 1 / (p : ℝ))| ≤ D := by
  calc
    _ = |∑ p ∈ P ∩ Q, (q p - (1 / 2 : ℝ) / p)| := by
      congr 1
      rw [sum_sub_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p ∈ P ∩ Q, |q p - (1 / 2 : ℝ) / p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, |q p - (1 / 2 : ℝ) / p| :=
      sum_le_sum_of_subset_of_nonneg inter_subset_left (fun _ _ _ => abs_nonneg _)
    _ ≤ D := hD

/-- A bounded total parameter error changes either signed exponential factor
by at most exp D, uniformly for exp s <= 2. -/
theorem exponential_mean_error {m M s r D : ℝ} (_hD : 0 ≤ D)
    (hmean : |m - M / 2| ≤ D) (hs : Real.exp s ≤ 2) :
    Real.exp (-s * r + (Real.exp s - 1) * m) ≤
      Real.exp D * Real.exp (-s * r + ((Real.exp s - 1) / 2) * M) := by
  have habs : |Real.exp s - 1| ≤ 1 := abs_le.mpr ⟨by linarith [Real.exp_pos s], by linarith⟩
  have hprod : |(Real.exp s - 1) * (m - M / 2)| ≤ D := by
    rw [abs_mul]
    exact (mul_le_mul habs hmean (abs_nonneg _) (by norm_num)).trans_eq (one_mul D)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hu := (abs_le.mp hprod).2
  nlinarith only [hu]

/-- At the full cutoff the sieve mass is just the actual prime reciprocal
mass, so the same Chernoff factors bound the indicator probabilities. -/
theorem full_cutoff_prime_mass (B : ℕ) (Q : Finset ℕ)
    (hP : 6 ≤ auxiliaryCutoff B) :
    tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q =
      ∑ p ∈ auxiliaryPrimes B ∩ Q, 1 / (p : ℝ) := by
  classical
  have hset : (sievePrimes (sieveCutoff 4 B)).filter
      (fun p => auxiliaryCutoff B < p ∧ p ∈ Q) = auxiliaryPrimes B ∩ Q := by
    ext p
    simp only [mem_filter, mem_inter, sievePrimes, auxiliaryPrimes, auxiliaryUpper,
      sieveCutoff, largePrimeSet, mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hpZ, hp⟩, _hp6⟩, hpP, hpQ⟩
      exact ⟨⟨⟨hpZ, hp⟩, by exact_mod_cast hpP⟩, hpQ⟩
    · rintro ⟨⟨⟨hpZ, hp⟩, hpP⟩, hpQ⟩
      have hPp : auxiliaryCutoff B < p := by exact_mod_cast hpP
      exact ⟨⟨⟨hpZ, hp⟩, by omega⟩, hPp, hpQ⟩
  unfold tiltPrimeReciprocalMass
  rw [hset]

theorem bernoulli_count_tail_stable (B : ℕ) (Q : Finset ℕ) (q : ℕ → ℝ)
    (s r : ℝ) {D : ℝ} (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : Real.exp s ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if s * r ≤ s * (S ∩ Q).card then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * Real.exp (-s * r + ((Real.exp s - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q) := by
  have hmean := restricted_indicator_mean_error (auxiliaryPrimes B) Q q herr
  rw [← full_cutoff_prime_mass B Q hP] at hmean
  have hmean' : |(∑ p ∈ auxiliaryPrimes B ∩ Q, q p) -
      tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q / 2| ≤ D := by
    convert hmean using 1
    congr 1
    ring
  exact (bernoulliSubsetMass_restricted_count_tail _ Q q s r hq).trans
    (exponential_mean_error hD hmean' hs)

end JointDickman

end OAI
