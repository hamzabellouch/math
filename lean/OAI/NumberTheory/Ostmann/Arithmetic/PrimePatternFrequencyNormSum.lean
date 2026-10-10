import OAI.NumberTheory.Ostmann.Arithmetic.PatternFrequencyNormSum
import OAI.NumberTheory.Ostmann.Arithmetic.PrimePatternUniformBudget

namespace OAI

/-! # Summing two-prime arithmetic coefficients with their actual pattern cost -/

namespace Ostmann
open scoped Classical BigOperators

/-- The same retained frequency sum survives summing every equality pattern
of the original internal prime samples. -/
theorem prime_pattern_frequency_norm_sum_le (S : Finset ℤ) (n N V : ℕ)
    (D E K err : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hK : 0 ≤ K) (herr : 0 ≤ err)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    ∀ R : Setoid (Bool × MovingSampleIndex n) → FrequencyTree (S × S) n → ℂ,
    (∀ s t, ‖R s t‖ ≤
      ((4 : ℝ) ^ Fintype.card (Quotient s) * E ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
        (err + K * (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod))) →
    ‖∑ s, ∑ t, R s t‖ ≤
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) * (max 4 E) ^ (4 * n * 2 ^ n)) *
        ((Fintype.card (FrequencyTree (S × S) n) : ℝ) * err +
          K * ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) := by
  dsimp only
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  intro R hR
  let T : ℝ := (Fintype.card (FrequencyTree (S × S) n) : ℝ) * err +
    K * ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
      (2 * (V : ℝ)) ^ (2 * 2 ^ n))
  have hlog := Real.log_natCast_nonneg N
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hs (s : Setoid (Bool × MovingSampleIndex n)) :
      ‖∑ t, R s t‖ ≤ T * ((4 : ℝ) ^ Fintype.card (Quotient s) *
        E ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) := by
    let κ : ℝ := (4 : ℝ) ^ Fintype.card (Quotient s) *
      E ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))
    have hκ : 0 ≤ κ := mul_nonneg (by positivity) (pow_nonneg hE _)
    have h := paired_frequency_norm_sum_le S n N V D (κ * K) (κ * err) hD
      (mul_nonneg hκ hK) hS hdiv (R s) (fun t => by
        simpa only [κ, mul_add, mul_assoc] using hR s t)
    exact h.trans_eq (by dsimp only [T]; ring)
  have h := movingPattern_prime_error_sum_le n E T hE hT (fun s => ∑ t, R s t) hs
  exact h.trans_eq (by ring)

end Ostmann

end OAI
