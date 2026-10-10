import OAI.NumberTheory.TwoPoint.Bounds.QualitativeSieveParameters
import OAI.NumberTheory.TwoPoint.Bounds.RoughSieveProbability

namespace OAI

/-! The published Mertens estimate on the smaller qualitative sieve
cutoff, and the exact inclusion of its primes in the roughness condition. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def qualitativeSievePrimes (B : ℝ) : Finset ℕ :=
  sievePrimesUpTo (Real.exp (qualitativeSieveLogCutoff B))

def HasNoPrimeFactorBelow (R : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (p : ℝ) < R → ¬p ∣ n

lemma qualitativeSieveLogCutoff_lt_power (B : ℝ) (hB : 0 < B) :
    qualitativeSieveLogCutoff B < B ^ (9999 / 10000 : ℝ) := by
  apply div_lt_self (Real.rpow_pos_of_pos hB _)
  have hr : (0 : ℝ) ≤ qualitativeSieveHalfOrder B := Nat.cast_nonneg _
  push_cast
  nlinarith only [hr]

lemma HasNoPrimeFactorBelow.qualitativeSieve {B : ℝ} (hB : 0 < B) {n : ℕ}
    (hn : HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) n) :
    avoidsPrimeSet (qualitativeSievePrimes B) n := by
  intro p hp
  apply hn p (sievePrimesUpTo_prime _ p hp)
  exact (sievePrimesUpTo_le _ (Real.exp_pos _).le p hp).trans_lt
    (Real.exp_lt_exp.mpr (qualitativeSieveLogCutoff_lt_power B hB))

theorem PrimeReciprocalInput.qualitative_scale (hM : PrimeReciprocalInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℝ in atTop,
      |(∑ p ∈ qualitativeSievePrimes B, 1 / (p : ℝ)) -
        Real.log (qualitativeSieveLogCutoff B)| ≤ C ∧
      (∑ p ∈ qualitativeSievePrimes B, 1 / (p : ℝ)) ≤ (5 / 4 : ℝ) * Real.log B := by
  obtain ⟨C, hC⟩ := hM
  have hC₀ : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨C, hC₀, ?_⟩
  filter_upwards [eventually_qualitativeSieveParameters,
    eventually_ge_atTop (Real.exp (4 * C + 1))] with B hpar hB
  have hX : 0 < qualitativeSieveLogCutoff B := zero_lt_one.trans_le hpar.cutoff_one
  have hy : 2 ≤ Real.exp (qualitativeSieveLogCutoff B) := by
    linarith [Real.add_one_le_exp (qualitativeSieveLogCutoff B), hpar.cutoff_one]
  have hm := hC (Real.exp (qualitativeSieveLogCutoff B)) hy
  rw [Real.log_exp] at hm
  refine ⟨hm, ?_⟩
  have hlogC : 4 * C + 1 ≤ Real.log B := by
    rw [← Real.log_exp (4 * C + 1)]
    exact Real.log_le_log (Real.exp_pos _) hB
  have hlogX := Real.log_le_log hX hpar.cutoff_le
  have hu := (abs_le.mp hm).2
  change (∑ p ∈ qualitativeSievePrimes B, 1 / (p : ℝ)) -
    Real.log (qualitativeSieveLogCutoff B) ≤ C at hu
  linarith

end TwoPointCorrelations

end OAI
