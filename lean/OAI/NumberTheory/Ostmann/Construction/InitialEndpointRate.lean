import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Construction.HarmonicInitialAmplitude

namespace OAI

/-! # Uniform exponential rate in the positive endpoint lower bound -/

namespace Ostmann

open Filter

/-- The number of cell roles affects only the cutoff, not the final rate. -/
theorem eventual_endpoint_statistic_rate (r : ℕ) (c δ γ A B : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hγ : 0 < γ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ m : ℕ in atTop, ∀ (L u K : ℝ), L ≤ 2 * m → 0 < K →
      Real.exp (-A * L) ≤ u → K ≤ Real.exp (B * L) →
      Real.exp (-(2 * (A + 3 * B) - 2 * Real.log δ + 1) * m) ≤
        u / K * (c * (δ ^ (m + 1) / K) ^ 2 * γ ^ (2 * r)) := by
  have hfixed : 0 < c * δ ^ 2 * γ ^ (2 * r) := by positivity
  have hp := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_le_const hfixed
  filter_upwards [hp] with m hm L u K hL hK hu hbin
  change Real.exp (-(m : ℝ)) ≤ c * δ ^ 2 * γ ^ (2 * r) at hm
  have hu0 : 0 < u := (Real.exp_pos _).trans_le hu
  have hki : Real.exp (-B * L) ≤ K⁻¹ := by
    have h := inv_anti₀ hK hbin
    simpa only [Real.exp_neg, neg_mul] using h
  have hδpow : δ ^ (2 * m) = Real.exp (((2 * m : ℕ) : ℝ) * Real.log δ) := by
    rw [Real.exp_nat_mul, Real.exp_log hδ]
  have hform : u / K * (c * (δ ^ (m + 1) / K) ^ 2 * γ ^ (2 * r)) =
      u * (K⁻¹) ^ 3 * (c * δ ^ 2 * γ ^ (2 * r)) * δ ^ (2 * m) := by
    rw [pow_add, pow_one, show 2 * m = m * 2 by omega, pow_mul]
    simp only [div_eq_mul_inv]
    ring
  rw [hform, hδpow]
  calc
    _ ≤ Real.exp (-A * L) * (Real.exp (-B * L)) ^ 3 *
        Real.exp (-(m : ℝ)) * Real.exp (((2 * m : ℕ) : ℝ) * Real.log δ) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith
    _ ≤ u * (K⁻¹) ^ 3 * (c * δ ^ 2 * γ ^ (2 * r)) *
        Real.exp (((2 * m : ℕ) : ℝ) * Real.log δ) := by
      gcongr

end Ostmann

end OAI
