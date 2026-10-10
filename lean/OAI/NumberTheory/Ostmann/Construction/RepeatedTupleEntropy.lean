import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget

namespace OAI

/-! # The broad-prime normalization cancels the repeated-tuple entropy -/
namespace Ostmann
open Filter

/-- There are two copies of the `m` broad positions and a fixed number of
cell roles. The `L^(-2m)` in their actual prior removes the `m log m` cost. -/
theorem eventual_repeated_tuple_entropy (r : ℕ) (z : ℝ) (hz : 0 < z) :
    ∀ᶠ m : ℕ in atTop, ∀ L : ℝ, 0 < L → (m : ℝ) ≤ z * L →
      ((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r)) / L ^ (2 * m) ≤
        Real.exp ((2 * Real.log (4 * z) + 1) * m) := by
  have hpoly := eventual_polynomial_log_budget ((4 : ℝ) ^ (2 * r)) 1 1 1 (2 * r)
    (by positivity) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hpoly,
    eventually_ge_atTop (max r 1)] with m hpoly hm L hL hmL
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmr : (r : ℝ) ≤ m := by exact_mod_cast (le_max_left r 1).trans hm
  have hn : ((2 * (m + r) : ℕ) : ℝ) ≤ 4 * m := by push_cast; linarith
  have hpow : (4 * (m : ℝ)) ^ (2 * r) ≤ Real.exp (m : ℝ) := by
    have hp := hpoly m hm0 (by simp)
    simp only [one_mul] at hp
    calc
      _ = (4 : ℝ) ^ (2 * r) * (m : ℝ) ^ (2 * r) := by rw [mul_pow]
      _ ≤ (4 : ℝ) ^ (2 * r) * (1 + (m : ℝ)) ^ (2 * r) := by gcongr; linarith
      _ ≤ _ := hp
  have hratio : 4 * (m : ℝ) / L ≤ 4 * z := by
    rw [div_le_iff₀ hL]
    nlinarith only [hmL]
  have hlog : 0 < 4 * z := by positivity
  calc
    _ ≤ (4 * (m : ℝ)) ^ (2 * (m + r)) / L ^ (2 * m) := by
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn _) (by positivity)
    _ = (4 * (m : ℝ) / L) ^ (2 * m) * (4 * (m : ℝ)) ^ (2 * r) := by
      rw [show 2 * (m + r) = 2 * m + 2 * r by omega, pow_add, div_pow]
      ring
    _ ≤ (4 * z) ^ (2 * m) * Real.exp (m : ℝ) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hratio _) hpow (by positivity) (by positivity)
    _ = Real.exp ((2 * Real.log (4 * z) + 1) * m) := by
      have he : (4 * z) ^ (2 * m) = Real.exp (((2 * m : ℕ) : ℝ) * Real.log (4 * z)) := by
        rw [Real.exp_nat_mul, Real.exp_log hlog]
      rw [he, ← Real.exp_add]
      congr 1
      push_cast
      ring

end Ostmann

end OAI
