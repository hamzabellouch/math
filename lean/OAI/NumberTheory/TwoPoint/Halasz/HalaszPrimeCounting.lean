import OAI.NumberTheory.Jacobsthal.Partitions.RealProgressionCoordinates

namespace OAI

/-! The short-interval prime-counting consequence needed for the weighted
Halasz mean-value argument, obtained by specializing the
Brun--Titchmarsh sieve to modulus one. -/

namespace TwoPointCorrelations

open Finset
open Erdos970.ErdosPrimeInputs

/-- Uniform upper bound for any finite set of primes in a real interval.
The location of the interval is unrestricted. -/
theorem halasz_prime_interval_bound : ∃ C B : ℝ, 0 < C ∧ 1 < B ∧
    ∀ (x H : ℝ) (P : Finset ℕ), B ≤ H →
      (∀ p ∈ P, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + H) →
      (P.card : ℝ) ≤ C * H / Real.log H := by
  classical
  obtain ⟨C, B, hC, hB, hupper⟩ := ProgressionPrimeUpper.progression_prime_upper
  refine ⟨C, B, hC, hB, ?_⟩
  intro x H P hBH hP
  have hH : 0 < H := lt_trans zero_lt_one (hB.trans_le hBH)
  obtain ⟨N, a, index, hcount, hcoord⟩ :=
    RealProgressionCoordinates.exists_coordinates x H 1 0 (by norm_num) hH.le
  let f : ℕ → ℕ := fun p => index (p : ℤ)
  have hdata : ∀ p ∈ P, f p < N ∧ AffinePrimeSieve.value a 1 (f p) = (p : ℤ) := by
    intro p hp
    obtain ⟨_, hlo, hhi⟩ := hP p hp
    exact hcoord (p : ℤ) (by exact_mod_cast hlo) (by exact_mod_cast hhi) (by
      rw [Int.modEq_iff_dvd]
      exact one_dvd _)
  have hinj : Set.InjOn f P := by
    intro p hp t ht heq
    have hz : (p : ℤ) = (t : ℤ) := (hdata p hp).2.symm.trans
      ((congrArg (AffinePrimeSieve.value a 1) heq).trans (hdata t ht).2)
    exact_mod_cast hz
  have hsub : P.image f ⊆ AffinePrimeSieve.primeIndices N a 1 := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (hdata p hp).1, ?_⟩
    rw [(hdata p hp).2]
    simpa only [Int.natAbs_natCast] using And.intro (hP p hp).1 (Int.natCast_nonneg p)
  have hc : P.card ≤ (AffinePrimeSieve.primeIndices N a 1).card := by
    calc
      _ = (P.image f).card := (card_image_iff.mpr hinj).symm
      _ ≤ _ := card_le_card hsub
  calc
    (P.card : ℝ) ≤ ((AffinePrimeSieve.primeIndices N a 1).card : ℝ) := by exact_mod_cast hc
    _ ≤ C * H / Real.log H := by
      simpa using hupper N a 1 H hBH (by norm_num) (by simpa using hcount)

end TwoPointCorrelations

end OAI
