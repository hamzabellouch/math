import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotPolynomial
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionShrink

namespace OAI

/-! Insignificant children are removed by the same radial shrink used in
the denominator comparison. There is no extra exceptional-child premise. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_insignificant_error (Q : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      L^Q*Real.exp (-L*Real.log L) ≤ SourceParameters.step L^(-(1/8:ℝ)) := by
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (2*Q),hlog]
    with L hL hQ hlog
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have h07 : L^(7/10:ℝ) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (7/10:ℝ) ≤ 1)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hb := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hstep : Real.log (SourceParameters.step L) ≤ 3*L := by
    have hb := (SourceParameters.log_step_bounds hL0.le).2
    linarith
  have hexponent : (Q-L)*Real.log L ≤ -(L/2) := by
    have hQL : Q-L ≤ -(L/2) := by linarith
    calc
      _ ≤ (-(L/2))*Real.log L := mul_le_mul_of_nonneg_right hQL (by linarith)
      _ ≤ -(L/2) := by nlinarith
  rw [Real.rpow_def_of_pos hL0,← Real.exp_add,
    Real.rpow_def_of_pos (SourceParameters.step_pos L)]
  apply Real.exp_le_exp.mpr
  calc
    _ = (Q-L)*Real.log L := by ring
    _ ≤ -(L/2) := hexponent
    _ ≤ Real.log (SourceParameters.step L)*(-(1/8:ℝ)) := by linarith

/-- A nonsignificant amplitude is zero in the graph snapshot, with the
same shrink radius that controls every displaced denominator. -/
theorem eventually_source_insignificant_shrink (Q : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (c : ℝ) (A : E), 0 ≤ c →
      ‖A‖ ≤ (L^Q*Real.exp (-L*Real.log L))*c →
      radialShrink (2*SourceParameters.step L^(-(1/8:ℝ))*c) A = 0 := by
  filter_upwards [eventually_source_insignificant_error Q] with L hL
  intro E _ _ c A hc hA
  apply source_prediction_shrink_zero hc (Real.rpow_nonneg (SourceParameters.step_pos L).le _) A
  exact hA.trans (mul_le_mul_of_nonneg_right hL hc)

end LipschitzHilbert

end

end OAI
