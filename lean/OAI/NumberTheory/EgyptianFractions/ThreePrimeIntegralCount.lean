import OAI.NumberTheory.EgyptianFractions.ThreePrimeContinuousFourier
import OAI.NumberTheory.EgyptianFractions.RationalSupplyReduction

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ThreePrimeContinuousFourier

/-- Positive prime frequencies up to the integer under representation. -/
def primeFrequencies (u : ℕ) : Finset ℕ := (Finset.Icc 1 u).filter Nat.Prime

/-- The unweighted positive-sign prime exponential sum. -/
def primePhaseSum (u : ℕ) (x : ℝ) : ℂ :=
  ∑ p ∈ primeFrequencies u, phase (p : ℤ) x

lemma prime_triples_eq_filter (u : ℕ) :
    supplyPrimeTriples u =
      ((primeFrequencies u) ×ˢ ((primeFrequencies u) ×ˢ (primeFrequencies u))).filter
        (fun t => t.1 + t.2.1 + t.2.2 = u) := by
  ext t
  simp only [supplyPrimeTriples, primeFrequencies, Finset.mem_filter, Finset.mem_product]
  tauto

/-- The exact prime-triple count is a continuous cubic Fourier coefficient.
This does not estimate the integral or assert a prime-distribution result. -/
theorem prime_triple_integral (u : ℕ) :
    (∫ x in (0 : ℝ)..1, primePhaseSum u x ^ 3 * phase (-(u : ℤ)) x) =
      ((supplyPrimeTriples u).card : ℂ) := by
  classical
  have h := weighted_triple_finset_integral (primeFrequencies u)
    (fun p : ℕ => (p : ℤ)) (fun _ => (1 : ℂ)) (u : ℤ)
  simp only [one_mul, mul_one] at h
  change (∫ x in (0 : ℝ)..1,
      (∑ p ∈ primeFrequencies u, phase (p : ℤ) x) ^ 3 * phase (-(u : ℤ)) x) = _
  rw [h, prime_triples_eq_filter]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  have heq : ((a : ℤ) + (b : ℤ) + (c : ℤ) = (u : ℤ)) ↔ a + b + c = u := by omega
  simp [heq]

end Problem337.ThreePrimeContinuousFourier

end

end OAI
