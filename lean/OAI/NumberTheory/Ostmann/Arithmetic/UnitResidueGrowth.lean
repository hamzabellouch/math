import Mathlib.Analysis.Real.Sqrt
import OAI.NumberTheory.Ostmann.Preliminaries.DivisorPowerBound

namespace OAI

/-! # Uniform square-root growth of the number of quadratic unit roots -/

namespace Ostmann

theorem exists_unit_residue_sqrt_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≠ 0 →
      (2 : ℝ) ^ (m.primeFactors.card + 1) ≤ C * Real.sqrt m := by
  obtain ⟨D, hD, hbound⟩ := exists_divisors_power_bound 2
  refine ⟨2 * Real.sqrt D, by positivity, ?_⟩
  intro m hm
  have hω : (2 : ℝ) ^ m.primeFactors.card ≤ m.divisors.card := by
    exact_mod_cast two_pow_primeFactors_card_le_divisors_card m hm
  have htau : (m.divisors.card : ℝ) ^ 2 ≤ (D : ℝ) * m := by
    exact_mod_cast hbound m hm
  have hsq : ((2 : ℝ) ^ m.primeFactors.card) ^ 2 ≤ (D : ℝ) * m :=
    (pow_le_pow_left₀ (by positivity) hω 2).trans htau
  have hs := Real.le_sqrt_of_sq_le hsq
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ D)] at hs
  rw [pow_succ]
  nlinarith

end Ostmann

end OAI
