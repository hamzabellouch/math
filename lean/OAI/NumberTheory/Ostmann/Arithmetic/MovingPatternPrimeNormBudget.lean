import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantErrorRate

namespace OAI

/-! # Joining the giant error to the sharp original arithmetic budget -/

namespace Ostmann
open Filter

/-- The exact harmonic denominator can be discarded only after positivity.
The giant comparison adds one error and leaves the sharp Fourier main term
and its internal-class weight intact. -/
theorem movingPattern_original_prime_norm_budget (n : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (c : ℕ) (E U u r cost main bulk a : ℝ),
      c ≤ 4 * n * 2 ^ n → 1 ≤ E → E ≤ Real.exp (C * L) →
      0 ≤ U → U ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
      1 ≤ u → 1 ≤ r → 0 ≤ cost → 0 ≤ main → 0 ≤ bulk →
      cost ≤ Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) →
      bulk ≤ Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) →
      a ≤ ((2 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c) * U ^ c) *
          (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
            Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) +
        ((4 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c)) * (cost + main + bulk) / (u * r) →
      a ≤ ((4 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c)) *
        (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) + main) := by
  filter_upwards [movingPattern_giant_error_rate n C hC] with L hgiant
  intro c E U u r cost main bulk a hc hE hEup hU hUup hu hr hcost hmain hbulk
    hcostup hbulkup ha
  let κ := (4 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c)
  have hκ : 1 ≤ κ := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ hE)
  have hκ0 : 0 ≤ κ := by linarith
  have hden : 1 ≤ u * r := one_le_mul_of_one_le_of_one_le hu hr
  have hn : 0 ≤ κ * (cost + main + bulk) := by positivity
  have hdiv := div_le_self hn hden
  have hsmall := hgiant c hc E U (by linarith) hEup hU hUup
  have hmove : Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) ≤
      κ * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) :=
    le_mul_of_one_le_left (Real.exp_nonneg _) hκ
  have hcost' := mul_le_mul_of_nonneg_left hcostup hκ0
  have hbulk' := mul_le_mul_of_nonneg_left hbulkup hκ0
  change a ≤ κ * _
  change a ≤ _ + κ * (cost + main + bulk) / (u * r) at ha
  nlinarith only [ha, hdiv, hsmall, hmove, hcost', hbulk']

end Ostmann

end OAI
