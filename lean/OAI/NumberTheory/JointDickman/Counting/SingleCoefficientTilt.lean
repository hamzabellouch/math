import OAI.NumberTheory.JointDickman.Arithmetic.SingleFormSieve
import OAI.NumberTheory.JointDickman.Amplification.WeightedCountTail

namespace OAI

/-! # Exponential count moments for one actual coefficient -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem single_tilted_density_normalization
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ B Z : ℕ, 1 < B → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      ∀ (Q : Finset ℕ) (s : ℝ), Real.exp s ≤ 2 →
      coefficientScale B * tiltedSieveDensity (auxiliaryCutoff B) Z Q s ≤
      M * Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) := by
  obtain ⟨C, hC, hbound⟩ := coefficient_sieve_density_bound hM hδ
  refine ⟨C * Real.exp 4, by positivity, ?_⟩
  intro B Z hB hPZ hlog Q s hs
  calc
    _ ≤ coefficientScale B * (roughSieveDensity (auxiliaryCutoff B) Z *
        Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q + 4)) :=
      mul_le_mul_of_nonneg_left (tilted_sieve_density_bound _ _ Q hs) (coefficientScale_nonneg B)
    _ = (coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z) *
        Real.exp 4 * Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := by gcongr; exact hbound B Z hB hPZ hlog

theorem single_coefficient_exp_moment
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z u v : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z → u ≤ v →
      ∀ (Q : Finset ℕ) (s : ℝ), Real.exp s ≤ 2 →
      (∑ n ∈ Ico u v, tiltedCoefficientWeight B Q s n) ≤
      C * ((v : ℝ) - u) * Real.exp (((Real.exp s - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) +
      coefficientScale B * (2 * (Z + 1 : ℝ) * Z) := by
  obtain ⟨Cs, hCs, hsieve⟩ := single_form_interval_sieve hFord hM
  obtain ⟨M, hMpos, hnorm⟩ := single_tilted_density_normalization hM hδ
  refine ⟨Cs * M, mul_pos hCs hMpos, ?_⟩
  intro B Z u v hB hZ hPZ hlog huv Q s hs
  have hP : ∀ p ∈ sievePrimes Z, p.Prime ∧ p ≤ Z ∧ 2 ≤ p := by
    intro p hp
    obtain ⟨hpZ, hp6⟩ := mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hpZ).2, (Nat.mem_primesLE.mp hpZ).1, by omega⟩
  have hb := hsieve (sievePrimes Z) (tiltedSieveTheta (auxiliaryCutoff B) Q s) u v Z huv hZ hP
    (fun p _ => tiltedSieveTheta_bounds _ Q hs p)
  have hlen : 0 ≤ (v : ℝ) - u := sub_nonneg.mpr (by exact_mod_cast huv)
  have hmain := mul_le_mul_of_nonneg_left (hnorm B Z hB hPZ hlog Q s hs)
    (mul_nonneg hCs.le hlen)
  calc
    _ ≤ ∑ n ∈ Ico u v, coefficientScale B *
        ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) :=
      sum_le_sum (fun n _ => tiltedCoefficientWeight_le_sieved B Z Q hs n)
    _ = coefficientScale B * (∑ n ∈ Ico u v,
        ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p)) :=
      (mul_sum _ _ _).symm
    _ ≤ coefficientScale B * (Cs * ((v : ℝ) - u) *
        tiltedSieveDensity (auxiliaryCutoff B) Z Q s + 2 * (Z + 1 : ℝ) * Z) :=
      mul_le_mul_of_nonneg_left hb (coefficientScale_nonneg B)
    _ ≤ _ := by
      dsimp only [tiltedSieveDensity] at hmain ⊢
      nlinarith only [hmain]

theorem single_coefficient_count_tail
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z u v : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z → u ≤ v →
      ∀ (Q : Finset ℕ) (s r : ℝ), Real.exp s ≤ 2 →
      (∑ n ∈ Ico u v, if s * r ≤ s * primeDivisorCount Q n then coefficientWeight B n else 0) ≤
      C * ((v : ℝ) - u) * Real.exp (-s * r + ((Real.exp s - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) +
      Real.exp (-s * r) * coefficientScale B * (2 * (Z + 1 : ℝ) * Z) := by
  obtain ⟨C, hC, hbound⟩ := single_coefficient_exp_moment hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B Z u v hB hZ hPZ hlog huv Q s r hs
  have hm := weighted_exp_markov (Ico u v) (coefficientWeight B) (fun n => primeDivisorCount Q n) s r
    (fun n _ => coefficientWeight_nonneg B n)
  have hb := mul_le_mul_of_nonneg_left (hbound B Z u v hB hZ hPZ hlog huv Q s hs)
    (Real.exp_pos (-s * r)).le
  have h := hm.trans hb
  simpa only [tiltedCoefficientWeight, mul_add, Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using h

end JointDickman

end OAI
