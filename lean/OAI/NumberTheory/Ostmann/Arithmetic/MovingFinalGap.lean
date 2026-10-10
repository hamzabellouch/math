import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Construction.DiagonalGapBudget

namespace OAI

/-! # The polynomial bulk scale leaves a strict final overlap margin -/

namespace Ostmann
open Filter Asymptotics

/-- At the manuscript's scale `z = k^4`, every fixed logarithmic cost is
smaller than any fixed positive multiple of `log (2^k)`. -/
theorem eventually_polynomial_scale_log_margin (B C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop,
      B + C * Real.log ((k : ℝ) ^ 4) < δ * Real.log ((2 : ℝ) ^ k) := by
  have hlog := (((Real.isLittleO_log_id_atTop.const_mul_left (4 * C)).add
    (isLittleO_const_id_atTop B)).bound
    (by positivity : 0 < δ * Real.log 2 / 2))
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlog,
    eventually_ge_atTop (1 : ℕ)] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  simp only [Real.norm_eq_abs, id_eq, abs_of_pos hk0] at hk
  rw [Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have h := (le_abs_self _).trans hk
  have hpos : 0 < δ * Real.log 2 * (k : ℝ) := by positivity
  nlinarith

/-- The `3/4` bad-arrangement saving dominates the `2/5` cutoff exponent,
with the full base-gap and fixed logarithmic costs of (9.8). -/
theorem eventually_moving_final_gap (Bs BD Bz C B : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      BD + 2 * Bs + (Bz + 16) * Real.log ((k : ℝ) ^ 4) + C + 2 * B + 2 <
        (7 / 20 : ℝ) * Real.log ((2 : ℝ) ^ k) := by
  filter_upwards [eventually_polynomial_scale_log_margin (BD + 2 * Bs + C + 2 * B + 2)
    (Bz + 16) (7 / 20) (by norm_num)] with k hk
  linarith

end Ostmann

end OAI
