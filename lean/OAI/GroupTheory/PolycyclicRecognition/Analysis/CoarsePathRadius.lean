import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathConcatenation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! # Radius control for logarithmic-error paths

The support-path parameter bounds imply a single linear ambient ball bound
for every sample, uniformly at all scales at least one.
-/

namespace PolycyclicRecognition

variable {X : Type*} [PseudoMetricSpace X] {x y : X}

/-- A coarse path stays within its speed plus its additive error of its source. -/
theorem PathMetricBound.dist_source_le {p : Path x y} {L κ : ℝ}
    (h : PathMetricBound p L κ) (hL : 0 ≤ L) (t : unitInterval) :
    dist x (p t) ≤ L + κ := by
  have hb := h 0 t
  rw [Path.source, Set.Icc.coe_zero, zero_sub, abs_neg,
    abs_of_nonneg t.property.1] at hb
  exact hb.trans (by nlinarith [t.property.2])

/-- The logarithmic error is uniformly at most a linear error for `r ≥ 1`. -/
theorem PathMetricBound.dist_source_le_linear {p : Path x y} {C r : ℝ}
    (h : PathMetricBound p (C * r) (C * (1 + Real.log (2 + r))))
    (hC : 0 ≤ C) (hr : 1 ≤ r) (t : unitInterval) :
    dist x (p t) ≤ (4 * C) * r := by
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + r)
  have hb := h.dist_source_le (mul_nonneg hC (by linarith)) t
  have hh : 1 + Real.log (2 + r) ≤ 3 * r := by linarith
  have hm := mul_le_mul_of_nonneg_left hh hC
  nlinarith

end PolycyclicRecognition

end OAI
