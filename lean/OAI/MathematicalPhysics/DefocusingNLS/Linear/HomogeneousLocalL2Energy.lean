import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # The exact physical local L² norm and radius monotonicity -/

open MeasureTheory Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousLocalL2Observation_norm_sq (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) :
    ‖homogeneousLocalL2Observation a k R ha ha1 hk u‖ ^ 2 =
      ∫ x in Metric.closedBall (0 : E) R, ‖homogeneousPhysicalCLM a k ha ha1 hk u x‖ ^ 2 := by
  let f := homogeneousLocalL2Observation a k R ha ha1 hk u
  have h := real_inner_self_eq_norm_sq f
  rw [L2.inner_def] at h
  calc
    ‖f‖ ^ 2 = ∫ x : Metric.closedBall (0 : E) R,
        ‖homogeneousPhysicalCLM a k ha ha1 hk u x‖ ^ 2 ∂homogeneousBallMeasure R := by
      rw [← h]
      apply integral_congr_ae
      filter_upwards [homogeneousLocalL2Observation_ae a k R ha ha1 hk u] with x hx
      change inner ℝ (f x) (f x) = _
      rw [show f x = homogeneousPhysicalCLM a k ha ha1 hk u x from hx,
        real_inner_self_eq_norm_sq]
    _ = _ := by
      unfold homogeneousBallMeasure
      rw [integral_subtype_comap measurableSet_closedBall
        (fun x : E => ‖homogeneousPhysicalCLM a k ha ha1 hk u x‖ ^ 2),
        Measure.restrict_restrict measurableSet_closedBall, inter_self]

theorem homogeneousLocalL2Observation_norm_mono (a k R S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hRS : R ≤ S) (u : HomogeneousY a k) :
    ‖homogeneousLocalL2Observation a k R ha ha1 hk u‖ ≤
      ‖homogeneousLocalL2Observation a k S ha ha1 hk u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [homogeneousLocalL2Observation_norm_sq, homogeneousLocalL2Observation_norm_sq]
  apply setIntegral_mono_set
    (((homogeneousPhysicalCLM a k ha ha1 hk u).continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : E) S))
    (ae_of_all _ (fun x => sq_nonneg _))
  exact ae_of_all _ (fun x hx => (Metric.closedBall_subset_closedBall hRS) hx)

end DefocusingNLS

end OAI
