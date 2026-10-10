import Mathlib.Analysis.SpecialFunctions.Sqrt
import OAI.NumberTheory.Ostmann.Arithmetic.SquareRootProbability
import OAI.NumberTheory.Ostmann.Preliminaries.DivisorPowerBound

namespace OAI

/-! # A sufficient reciprocal-totient bound for the large-modulus range -/

namespace Ostmann

theorem reciprocal_totient_sqrt_bound : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q →
    1 / (q.totient : ℝ) ≤ C / Real.sqrt q := by
  obtain ⟨D, hD, hdiv⟩ := exists_divisors_power_bound 2
  refine ⟨Real.sqrt D, Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < D by omega)), ?_⟩
  intro q hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hτ : (q : ℝ) ≤ q.divisors.card * (q.totient : ℝ) := by
    exact_mod_cast le_divisors_card_mul_totient q hq.ne'
  have hdiv' : (q.divisors.card : ℝ) ^ 2 ≤ D * (q : ℝ) := by exact_mod_cast hdiv q hq.ne'
  have hq2 : (q : ℝ) ^ 2 ≤ (D : ℝ) * q * (q.totient : ℝ) ^ 2 := by
    have hs : (q : ℝ) ^ 2 ≤ (q.divisors.card * (q.totient : ℝ)) ^ 2 := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hdiv' (sq_nonneg (q.totient : ℝ))
    nlinarith
  have hqD : (q : ℝ) ≤ (D : ℝ) * (q.totient : ℝ) ^ 2 := by nlinarith
  have hs := Real.sqrt_le_sqrt hqD
  rw [Real.sqrt_mul (Nat.cast_nonneg D), Real.sqrt_sq_eq_abs,
    abs_of_pos hφ] at hs
  exact (div_le_div_iff₀ hφ (Real.sqrt_pos.mpr hqpos)).mpr (by simpa using hs)

end Ostmann

end OAI
