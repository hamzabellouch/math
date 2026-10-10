import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCompactObservation
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

namespace OAI

/-! # Compact local L² observation

The measure is ordinary Lebesgue measure on the closed Euclidean ball.
The observation agrees almost everywhere with the actual physical Fourier
realization and is compact by the already proved uniform local observation.
-/

open MeasureTheory Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousBallMeasure (R : ℝ) :
    Measure (Metric.closedBall (0 : E) R) :=
  (volume.restrict (Metric.closedBall (0 : E) R)).comap Subtype.val

instance homogeneousBallMeasure_finite (R : ℝ) :
    IsFiniteMeasure (homogeneousBallMeasure R) := by
  unfold homogeneousBallMeasure
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : E) R).measure_lt_top.ne
  infer_instance

noncomputable def homogeneousLocalL2Observation (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    HomogeneousY a k →L[ℂ] Lp ℂ 2 (homogeneousBallMeasure R) :=
  (BoundedContinuousFunction.toLp 2 (homogeneousBallMeasure R) ℂ).comp
    (homogeneousLocalObservation a k ha ha1 hk (Metric.closedBall 0 R))

theorem homogeneousLocalL2Observation_ae (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    homogeneousLocalL2Observation a k R ha ha1 hk f =ᵐ[homogeneousBallMeasure R]
      (fun x => homogeneousPhysicalCLM a k ha ha1 hk f x) :=
  BoundedContinuousFunction.coeFn_toLp 2 (homogeneousBallMeasure R) ℂ _

theorem isCompactOperator_homogeneousLocalL2Observation (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    IsCompactOperator (homogeneousLocalL2Observation a k R ha ha1 hk) := by
  exact (isCompactOperator_homogeneousLocalObservation a k ha ha1 hk
    (Metric.closedBall 0 R)).clm_comp
      (BoundedContinuousFunction.toLp 2 (homogeneousBallMeasure R) ℂ)

end DefocusingNLS

end OAI
