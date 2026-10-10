import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalL2
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalInjective
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! # Local physical L² observations separate the faithful Y space -/

open MeasureTheory Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousLocalL2_zero_on_ball (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k)
    (hu : homogeneousLocalL2Observation a k R ha ha1 hk u = 0) :
    EqOn (homogeneousPhysicalCLM a k ha ha1 hk u) 0 (Metric.ball (0 : E) R) := by
  have hsub : ∀ᵐ x : Metric.closedBall (0 : E) R ∂homogeneousBallMeasure R,
      homogeneousPhysicalCLM a k ha ha1 hk u x = 0 := by
    filter_upwards [homogeneousLocalL2Observation_ae a k R ha ha1 hk u,
      Lp.coeFn_zero ℂ 2 (homogeneousBallMeasure R)] with x hx hz
    rw [hu] at hx
    exact hx.symm.trans hz
  have hclosed : ∀ᵐ x : E ∂volume.restrict (Metric.closedBall (0 : E) R),
      homogeneousPhysicalCLM a k ha ha1 hk u x = 0 := by
    have h := (ae_restrict_iff_subtype (μ := volume.restrict (Metric.closedBall (0 : E) R))
      (p := fun x : E => homogeneousPhysicalCLM a k ha ha1 hk u x = 0)
      measurableSet_closedBall).mpr hsub
    simpa only [Measure.restrict_restrict measurableSet_closedBall, inter_self] using h
  have hopen := ae_restrict_of_ae_restrict_of_subset Metric.ball_subset_closedBall hclosed
  exact Measure.eqOn_open_of_ae_eq hopen Metric.isOpen_ball
    (homogeneousPhysicalCLM a k ha ha1 hk u).continuous.continuousOn continuous_const.continuousOn

theorem homogeneousLocalL2_observations_separate (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k)
    (hu : ∀ R : ℝ, 0 < R → homogeneousLocalL2Observation a k R ha ha1 hk u = 0) :
    u = 0 := by
  apply homogeneousPhysicalCLM_injective a k ha ha1 hk
  rw [map_zero]
  apply DFunLike.ext
  intro x
  have he := homogeneousLocalL2_zero_on_ball a k (‖x‖ + 1) ha ha1 hk u
    (hu (‖x‖ + 1) (by positivity))
  exact he (by simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖)

end DefocusingNLS

end OAI
