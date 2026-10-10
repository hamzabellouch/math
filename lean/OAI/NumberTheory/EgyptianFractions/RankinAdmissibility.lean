import OAI.NumberTheory.EgyptianFractions.RankinBand

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The intermediate-band Rankin exponent is admissible throughout the scale window. -/
theorem rankin_band_exponent_admissible (S v t : ℝ)
    (hS : 1 < S) (ht : 1 ≤ t) (htv : t ≤ v)
    (hv : v ≤ S ^ 2) (hlow : 4 * Real.log S ≤ t) :
    Real.log (v / t) / (10 * t) ≤ 1 / 4 := by
  have hSpos : 0 < S := by linarith
  have htpos : 0 < t := by linarith
  have hvpos : 0 < v := by linarith
  have hquot : v / t ≤ S ^ 2 := by
    apply (div_le_iff₀ htpos).mpr
    nlinarith [sq_nonneg S]
  have hlog := Real.log_le_log (div_pos hvpos htpos) hquot
  rw [Real.log_pow] at hlog
  apply (div_le_iff₀ (by positivity : 0 < 10 * t)).mpr
  nlinarith

/-- Evaluated Rankin estimate with its exponent restriction discharged by scale bounds. -/
theorem divisor_rankin_intermediate_band_of_scale (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S v t : ℝ, 1 < S → 1 ≤ t → t ≤ v →
      v ≤ S ^ 2 → 4 * Real.log S ≤ t → ∀ s : Finset ℕ,
      (∀ n ∈ s, ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Real.exp (2 * t)) →
      (∀ n ∈ s, Real.exp (v / 5) ≤ (n : ℝ)) →
      (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-(v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := divisor_rankin_intermediate_band_of_prime_divisors r
  refine ⟨C, hC, ?_⟩
  intro S v t hS ht htv hv hlow s hprime hlarge
  exact hbound v t ht htv (rankin_band_exponent_admissible S v t hS ht htv hv hlow)
    s hprime hlarge

end Problem337

end

end OAI
