import OAI.Geometry.RCD.Coordinates.OverlappingExactFrames
import OAI.Geometry.RCD.Harmonic.RadialVolumeUnits
import OAI.Geometry.RCD.Metric.VolumeRigidityInput

namespace OAI

/-! # Exact frame comparison for nearby radial centers -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The quarter-error volume regime supplies the overlap ratio for two
nearby same-scale exact frames. The bound has no dependence on the scale. -/
theorem nearby_exact_frames {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (p q : X) {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε) (hdist : dist p q ≤ s / 4)
    (Np Nq : Euclidean n ≃L[ℝ] Euclidean n) (vp vq : X → Euclidean n)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (2 : ℝ) ^ n) * ε) ≤ 1 / 3)
    (hp : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2 * s) ε (transformedColumn (hausdorff n X) hX.quadratic u Np) vp)
    (hq : FirstOrderSplittingOn (hausdorff n X) hX.quadratic q (2 * s) ε (transformedColumn (hausdorff n X) hX.quadratic u Nq) vq)
    (hep : IsExactMeanNormalization (hausdorff n X) hX.quadratic (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p (2 * s)) measurableSet_ball Np)
    (heq : IsExactMeanNormalization (hausdorff n X) hX.quadratic (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball q (2 * s)) measurableSet_ball Nq)
    (hVp : |(hausdorff n X).real (ball p (2 * s)) / (euclideanUnitVolume n * (2 * s) ^ n) - 1| ≤ 1 / 4)
    (hVq : |(hausdorff n X).real (ball q (2 * s)) / (euclideanUnitVolume n * (2 * s) ^ n) - 1| ≤ 1 / 4)
    (hVs : |(hausdorff n X).real (ball q s) / (euclideanUnitVolume n * s ^ n) - 1| ≤ 1 / 4) :
    ‖Np.symm.toContinuousLinearMap.comp Nq.toContinuousLinearMap‖ ≤ Real.sqrt 2 ∧
    ‖Nq.symm.toContinuousLinearMap.comp Np.toContinuousLinearMap‖ ≤ Real.sqrt 2 := by
  let μ := hausdorff n X
  let C := (5 / 3 : ℝ) * (2 : ℝ) ^ n
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hω := euclideanUnitVolume_pos n
  have hlo := (quarter_volume_bounds hs hω hVs).2.1
  have hvolume (y : X)
      (hy : |μ.real (ball y (2 * s)) / (euclideanUnitVolume n * (2 * s) ^ n) - 1| ≤ 1 / 4) :
      μ.real (ball y (2 * s)) ≤ C * μ.real (ball q s) := by
    have hhi := (quarter_volume_bounds (by positivity : 0 < 2 * s) hω hy).2.2
    have hcomp := mul_le_mul_of_nonneg_left hlo hC
    have hid : C * ((3 / 4 : ℝ) * euclideanUnitVolume n * s ^ n) =
        (5 / 4 : ℝ) * euclideanUnitVolume n * (2 * s) ^ n := by
      rw [mul_pow]
      dsimp only [C]
      ring
    rw [hid] at hcomp
    exact hhi.trans hcomp
  apply overlapping_exact_frames μ hX.quadratic u p q (2 * s) Np Nq hε hC hsmall vp vq hp hq hep heq
    (ball q s) measurableSet_ball
  · apply ball_subset_ball'
    rw [dist_comm q p]
    linarith
  · exact ball_subset_ball (by linarith)
  · exact ne_of_gt (hX.fullSupport q s hs)
  · exact ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  · exact ne_of_gt (hX.fullSupport p (2 * s) (by positivity))
  · exact ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  · exact ne_of_gt (hX.fullSupport q (2 * s) (by positivity))
  · exact ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  · exact hvolume p hVp
  · exact hvolume q hVq

end RegularPointCoordinates

end

end OAI
