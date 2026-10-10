import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

open Filter Topology

namespace RyserCoveringCounterexample.Selection

theorem tendsto_nat_pow_mul_exp_neg_mul (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun K : ℕ => (K : ℝ) ^ m * Real.exp (-δ * (K : ℝ)))
      atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.rpow_natCast] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) δ hδ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_nat_mul_exp_linear_sub_mul_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto
      (fun q : ℕ => (q : ℝ) *
        Real.exp (b * (q : ℝ) - a * (q : ℝ) * Real.log (q : ℝ)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun q : ℕ => a * Real.log (q : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop ha
  have hdom : Tendsto (fun q : ℕ => (q : ℝ) * Real.exp (-(q : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  refine squeeze_zero' ?_ ?_ hdom
  · exact Filter.Eventually.of_forall fun q : ℕ =>
      mul_nonneg (Nat.cast_nonneg q) (Real.exp_pos _).le
  · filter_upwards [hlog.eventually_ge_atTop (b + 1)] with q hq
    have hexp : b * (q : ℝ) - a * (q : ℝ) * Real.log (q : ℝ) ≤ -(q : ℝ) := by
      calc
        b * (q : ℝ) - a * (q : ℝ) * Real.log (q : ℝ)
            = (b - a * Real.log (q : ℝ)) * (q : ℝ) := by ring
        _ ≤ (-1) * (q : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg q)
        _ = -(q : ℝ) := by ring
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (Nat.cast_nonneg q)

theorem tendsto_geometric_tail {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun N : ℕ => r ^ N / (1 - r)) atTop (𝓝 0) := by
  simpa only [zero_div] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).div_const (1 - r)

end RyserCoveringCounterexample.Selection

end OAI
