import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

namespace OAI

/-!
# Updating the unsmoothed map

The exact algebraic identity in the smoothing iteration. The difference
between the true and smoothed metric increments is bilinear in the
smoothing tail and the new increment, with no square of the tail.
-/

noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def pullbackMetric (F : E → V) (x v w : E) : ℝ :=
  inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w)

def metricCrossTerm (F U : E → V) (x v w : E) : ℝ :=
  inner ℝ (fderiv ℝ F x v) (fderiv ℝ U x w) +
    inner ℝ (fderiv ℝ F x w) (fderiv ℝ U x v)

theorem pullbackMetric_add {F U : E → V} {x : E}
    (hF : DifferentiableAt ℝ F x) (hU : DifferentiableAt ℝ U x) (v w : E) :
    pullbackMetric (fun y => F y + U y) x v w =
      pullbackMetric F x v w + metricCrossTerm F U x v w +
        pullbackMetric U x v w := by
  simp only [pullbackMetric, metricCrossTerm, fderiv_fun_add hF hU,
    add_apply, inner_add_left, inner_add_right]
  rw [real_inner_comm (fderiv ℝ U x v) (fderiv ℝ F x w)]
  ring

theorem metricCrossTerm_sub {G S U : E → V} {x : E}
    (hG : DifferentiableAt ℝ G x) (hS : DifferentiableAt ℝ S x) (v w : E) :
    metricCrossTerm (fun y => G y - S y) U x v w =
      metricCrossTerm G U x v w - metricCrossTerm S U x v w := by
  simp only [metricCrossTerm, fderiv_fun_sub hG hS, sub_apply,
    inner_sub_left]
  ring

/-- Comparing increments at the true map and its smoothing requires only
one copy of the smoothing tail. -/
theorem unsmoothed_metric_increment {G S U : E → V} {x : E}
    (hG : DifferentiableAt ℝ G x) (hS : DifferentiableAt ℝ S x)
    (hU : DifferentiableAt ℝ U x) (v w : E) :
    pullbackMetric (fun y => G y + U y) x v w - pullbackMetric G x v w =
      pullbackMetric (fun y => S y + U y) x v w - pullbackMetric S x v w +
        metricCrossTerm (fun y => G y - S y) U x v w := by
  rw [pullbackMetric_add hG hU, pullbackMetric_add hS hU,
    metricCrossTerm_sub hG hS]
  ring

/-- The normalized error identity after the target amplitude is changed.
The hypotheses identify the old defect, new defect, and smoothed increment
error; they impose no estimate or existence assumption. -/
theorem normalized_defect_identity {G S U : E → V} {x : E}
    (hG : DifferentiableAt ℝ G x) (hS : DifferentiableAt ℝ S x)
    (hU : DifferentiableAt ℝ U x) (v w : E)
    (δ δ' target H Hs H' error : ℝ)
    (hold : δ ^ 2 * H = target - pullbackMetric G x v w)
    (hnew : δ' ^ 2 * H' = target - pullbackMetric (fun y => G y + U y) x v w)
    (herror : error = pullbackMetric (fun y => S y + U y) x v w -
      pullbackMetric S x v w - (δ ^ 2 * Hs - δ' ^ 2 * target)) :
    δ' ^ 2 * (H' - target) = δ ^ 2 * (H - Hs) - error -
      metricCrossTerm (fun y => G y - S y) U x v w := by
  have hi := unsmoothed_metric_increment hG hS hU v w
  nlinarith

end ClosedSurfaceR4.ExactCorrection

end

end OAI
