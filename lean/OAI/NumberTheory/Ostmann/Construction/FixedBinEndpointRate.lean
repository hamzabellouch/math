import OAI.NumberTheory.Ostmann.Construction.InitialEndpointRate

namespace OAI

/-! # A fixed word bin keeps its rate after selecting the finitely many cells -/
namespace Ostmann
open Filter

theorem eventual_fixed_bin_endpoint_rate (nc : ℕ) (c γ A B : ℝ)
    (hc : 0 < c) (hγ : 0 < γ) :
    ∀ᶠ m : ℕ in atTop, ∀ u ρ : ℝ,
      Real.exp (-A * m) ≤ u → Real.exp (-B * m) ≤ ρ →
      Real.exp (-(A + 2 * B + 1) * m) ≤ u * (c * ρ ^ 2 * γ ^ (2 * nc)) := by
  have hfixed : 0 < c * γ ^ (2 * nc) := by positivity
  have hsmall := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const hfixed)
  filter_upwards [hsmall] with m hm u ρ hu hρ
  change Real.exp (-(m : ℝ)) ≤ c * γ ^ (2 * nc) at hm
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le.trans hρ
  have hu0 : 0 ≤ u := (Real.exp_pos _).le.trans hu
  calc
    _ = Real.exp (-A * m) * (Real.exp (-B * m)) ^ 2 * Real.exp (-(m : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ u * ρ ^ 2 * (c * γ ^ (2 * nc)) := by
      exact mul_le_mul (mul_le_mul hu (pow_le_pow_left₀ (Real.exp_pos _).le hρ 2)
        (sq_nonneg _) hu0) hm (Real.exp_nonneg _) (mul_nonneg hu0 (sq_nonneg _))
    _ = _ := by ring

end Ostmann

end OAI
