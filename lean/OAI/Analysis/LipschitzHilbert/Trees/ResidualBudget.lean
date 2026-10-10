import OAI.Analysis.LipschitzHilbert.Trees.SourceAveraging
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Final source-parameter budgets for the marked and unary residual costs. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

/-- The mass cutoff is chosen after the fixed polynomial losses. Both
residual exponents in §10 are at most `-1/4`. -/
theorem residual_polynomial_budget {L A C μ : ℝ}
    (hL : 1 ≤ L) (hμ : μ ≤ 1 / 12) (hA : 0 ≤ A)
    (hchoice : 4 * (C + 1 / 2) ≤ A) :
    L ^ (1 / 2 : ℝ) * L ^ C * (L ^ A) ^ (-(1 / 3 : ℝ) + μ) ≤ 1 ∧
      L ^ (1 / 2 : ℝ) * L ^ C * (L ^ A) ^ (-(1 / 2 : ℝ) + μ) ≤ 1 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hM : 1 ≤ L ^ A := Real.one_le_rpow hL hA
  have hbase : L ^ (1 / 2 : ℝ) * L ^ C * (L ^ A) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add hL0, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  constructor
  · apply le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hM (by linarith : -(1 / 3 : ℝ) + μ ≤ -(1 / 4 : ℝ)))
      (by positivity)) hbase
  · apply le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hM (by linarith : -(1 / 2 : ℝ) + μ ≤ -(1 / 4 : ℝ)))
      (by positivity)) hbase

/-- The discarded-top error stays negligible after the source's
`exp(C sqrt L)` mass bound and any fixed polynomial loss. -/
theorem eventually_discarded_residual_small (p C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-L) * Real.exp (C * Real.sqrt L) * L ^ p ≤ 1 := by
  have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (1 / 2)
    (by norm_num)
  filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop (4 * C ^ 2),
    hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with L hL hlarge hsmall
  have hsq := Real.sq_sqrt hL
  have hr := Real.sqrt_nonneg L
  have hroot : 2 * C ≤ Real.sqrt L := by nlinarith
  have hlinear : C * Real.sqrt L ≤ L / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hr]
  calc
    _ = L ^ p * Real.exp (-L + C * Real.sqrt L) := by rw [Real.exp_add]; ring
    _ ≤ L ^ p * Real.exp (-(1 / 2 : ℝ) * L) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
        (Real.rpow_nonneg hL _)
    _ ≤ 1 := hsmall.le

/-- Any fixed polynomial times the source step's negative power tends to
zero. This pays for the cumulative marked prediction losses. -/
theorem source_polynomial_step_decay (a c : ℝ) (hc : 0 < c) :
    Tendsto (fun L : ℝ => L ^ a * SourceParameters.step L ^ (-c)) atTop (𝓝 0) := by
  have hmodel : Tendsto (fun L : ℝ => L ^ a * Real.exp (-c * L ^ (7 / 10 : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / (7 / 10)) c hc).comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    simp only [Function.comp_apply, ← Real.rpow_mul hL]
    congr 2
    ring
  apply squeeze_zero' ?_ ?_ hmodel
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact mul_nonneg (Real.rpow_nonneg hL _)
      (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hL _)
  rw [Real.rpow_def_of_pos (SourceParameters.step_pos L)]
  apply Real.exp_le_exp.mpr
  have hlog := (SourceParameters.log_step_bounds hL).1
  nlinarith

end LipschitzHilbert

end

end OAI
