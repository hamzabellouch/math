import OAI.Analysis.LipschitzHilbert.Estimates.CompactMollification

namespace OAI

/-! A fixed shrinking positive mollifier family. Its a.e. convergence
comes from the existing Lebesgue differentiation theorem. -/
noncomputable section
open MeasureTheory Filter Function
open scoped Convolution Topology Pointwise
namespace LipschitzHilbert.PacketRepresentation

def testMollifier (n : ℕ) : ContDiffBump (0 : ℝ×ℝ) where
  rIn := (1/((n:ℝ)+1))/2
  rOut := 1/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0<1/((n:ℝ)+1) := by positivity
    linarith only [h]

theorem testMollifier_radius_le_one (n : ℕ) : (testMollifier n).rOut≤1 := by
  change 1/((n:ℝ)+1)≤1
  exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α:=ℝ) n])

theorem testMollifier_radius_tendsto :
    Tendsto (fun n => (testMollifier n).rOut) atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem compactMollification_ae_tendsto (f : (ℝ×ℝ) → ℂ)
    (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) :
    ∀ᵐ z ∂planeMeasure, Tendsto (fun n => compactMollification (testMollifier n) f hf hc z)
      atTop (nhds (f z)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    testMollifier_radius_tendsto
    (Filter.Eventually.of_forall fun n => show (testMollifier n).rOut≤2*(testMollifier n).rIn from by
      change 1/((n:ℝ)+1)≤2*((1/((n:ℝ)+1))/2)
      linarith) hf.locallyIntegrable

theorem compactMollification_common_support (f : (ℝ×ℝ) → ℂ)
    (hf : Integrable f planeMeasure) (hc : HasCompactSupport f) (n : ℕ) :
    support (compactMollification (testMollifier n) f hf hc)⊆
      Metric.closedBall (0 : ℝ×ℝ) 1+tsupport f := by
  apply (compactMollification_support _ f hf hc).trans
  apply Set.add_subset_add _ subset_closure
  exact (Metric.ball_subset_ball (testMollifier_radius_le_one n)).trans Metric.ball_subset_closedBall

end LipschitzHilbert.PacketRepresentation

end

end OAI
