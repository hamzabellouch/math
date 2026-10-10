import OAI.Geometry.RCD.Harmonic.ActualProjectionOuter
import OAI.Geometry.RCD.Sobolev.SmallBallPoissonQuadratic
import OAI.Geometry.RCD.Harmonic.ScaledProjectionData
import OAI.Geometry.RCD.Coordinates.BoundedLocalCoordinates

namespace OAI

/-! # The geometric data for one actual two-center projection

The source measures, equal-Laplacian Poisson replacements and harmonic
coordinate estimates determine the affine projection and its residual.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Equal-Laplacian replacements and harmonic coordinates centered at the
second point, with their source and normalization bounds. -/
structure ActualProjectionConfiguration {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    [IsFiniteMeasureOnCompacts (hausdorff n X)] (κ B J C A Cχ epsilon H D L M : ℝ) where
  root : ℝ
  root_le_one : root ≤ 1
  first : X
  center : X
  firstSource : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ first root
  secondSource : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ center root
  firstReplacement : DyadicDistanceReplacements (hausdorff n X) hX.quadratic firstSource B J C
  secondReplacement : DyadicDistanceReplacements (hausdorff n X) hX.quadratic secondSource B J C
  index : ℕ
  room : dist center first ≤ distanceSourceRadius root index / 4
  curvature : -1 ≤ K * distanceSourceRadius root index ^ 2
  smallCurvature : -κ ≤ K * (distanceSourceRadius root index / 512) ^ 2
  laplacianBound : (n : ℝ) + κ * (4 * distanceSourceRadius root index) ^ 2 ≤ (n : ℝ) + 1
  coordinates : Fin n → SobolevSpace (hausdorff n X) hX.quadratic
  coordinateValues : X → Euclidean n
  harmonic : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
    (ball center (distanceSourceRadius root index / 4)) (coordinates j)
  gradient : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball center (distanceSourceRadius root index / 4)),
    localGamma (hausdorff n X) hX.quadratic (coordinates j) (coordinates j) x ≤ (1 + epsilon) ^ 2
  firstGradient : ∀ᵐ x ∂(hausdorff n X).restrict (ball center (distanceSourceRadius root index / 4)),
    localGamma (hausdorff n X) hX.quadratic (firstReplacement.replacement index)
      (firstReplacement.replacement index) x ≤ (A * distanceSourceRadius root index) ^ 2
  secondGradient : ∀ᵐ x ∂(hausdorff n X).restrict (ball center (distanceSourceRadius root index / 4)),
    localGamma (hausdorff n X) hX.quadratic (secondReplacement.replacement index)
      (secondReplacement.replacement index) x ≤ (A * distanceSourceRadius root index) ^ 2
  cutoff : GoodLaplacianCutoff (hausdorff n X) hX.quadratic center (distanceSourceRadius root index / 64) Cχ
  one : SobolevSpace (hausdorff n X) hX.quadratic
  oneRepresentative : SobolevSpace.toLp (hausdorff n X) hX.quadratic one =ᵐ[
    (hausdorff n X).restrict (ball center (distanceSourceRadius root index / 512))] fun _ => (1 : ℝ)
  volume : ∀ t : ℝ, 0 < t → t ≤ root →
    |(hausdorff n X).real (ball center t) / (euclideanUnitVolume n * t ^ n) - 1| ≤ 1 / 4
  sphere : (hausdorff n X) (sphere center (distanceSourceRadius root index / 2048)) = 0
  frame : Euclidean n ≃L[ℝ] Euclidean n
  frameBound : ‖(frame : Euclidean n →L[ℝ] Euclidean n)‖ ≤ M
  source : ℝ
  source_pos : 0 < source
  pairBudget : normalizedPoissonDefect (hausdorff n X) hX.quadratic firstSource index +
    normalizedPoissonDefect (hausdorff n X) hX.quadratic secondSource index ≤ source ^ 2
  affineBound : ∀ c a, |c| + distanceSourceRadius root index * ‖frame.symm a‖ ≤ H *
    ‖normalizeLocalL2 (hausdorff n X) (ball center (distanceSourceRadius root index / 2048))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (affineCoordinateMap (hausdorff n X) hX.quadratic coordinates
        (ball center (distanceSourceRadius root index / 2048))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖
  affineHalfBound : ∀ c a, |c| + distanceSourceRadius root index * ‖frame.symm a‖ ≤ H *
    ‖normalizeLocalL2 (hausdorff n X) (ball center (distanceSourceRadius root index / 4096))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (affineCoordinateMap (hausdorff n X) hX.quadratic coordinates
        (ball center (distanceSourceRadius root index / 4096))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖
  columnBound : ∀ b : Euclidean n, ∀ᵐ x ∂(hausdorff n X).restrict
    (ball center (distanceSourceRadius root index / 512)),
    |SobolevSpace.toLp (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates (frame b)) x| ≤
        L * distanceSourceRadius root index * ‖b‖
  radialColumns : Euclidean n →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic
  radialMatrix : Euclidean n →L[ℝ] Euclidean n
  radialRepresentative : ∀ b, SobolevSpace.toLp (hausdorff n X) hX.quadratic (radialColumns b) =ᵐ[
    (hausdorff n X).restrict (ball center (distanceSourceRadius root index / 512))]
    localGamma (hausdorff n X) hX.quadratic (secondReplacement.replacement index)
      (sobolevColumnMap (hausdorff n X) hX.quadratic coordinates b)
  radialFit : ∀ b, ‖normalizeLocalL2 (hausdorff n X) (ball center (distanceSourceRadius root index / 512))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball center (distanceSourceRadius root index / 512))
      (radialColumns (frame b) - sobolevColumnMap (hausdorff n X) hX.quadratic coordinates (radialMatrix (frame b))))‖ ≤
      D * distanceSourceRadius root index * ‖b‖ * source
  totalSource : ℝ
  totalSource_nonneg : 0 ≤ totalSource
  summable : Summable (normalizedPoissonDefect (hausdorff n X) hX.quadratic secondSource)
  totalBudget : (∑' j, normalizedPoissonDefect (hausdorff n X) hX.quadratic secondSource j) ≤ totalSource
  approximationError : ℝ
  approximationError_pos : 0 < approximationError
  measured : IsMeasuredEuclideanApproximation (hausdorff n X) n center
    (distanceSourceRadius root index) (1 / 1024) approximationError coordinateValues
  centered : coordinateValues center = 0
  representative : ∀ j, SobolevSpace.toLp (hausdorff n X) hX.quadratic
    (radiusScaledColumns (hausdorff n X) hX.quadratic (distanceSourceRadius root index) coordinates j) =ᵐ[
      (hausdorff n X).restrict (ball center ((1 / 1024) * distanceSourceRadius root index))]
      fun x => coordinateValues x j

namespace ActualProjectionConfiguration

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  [IsFiniteMeasureOnCompacts (hausdorff n X)]
  {κ B J C A Cχ epsilon H D L M : ℝ}

/-- The physical radius is the actual radius of the chosen replacement. -/
def radius (d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M) : ℝ :=
  distanceSourceRadius d.root d.index

theorem radius_pos (d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M) :
    0 < d.radius := distanceSourceRadius_pos d.secondSource.radius_pos d.index

theorem radius_le_root (d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M) :
    d.radius ≤ d.root := by
  have hh := distanceSourceRadius_outer_le d.secondSource.radius_pos.le d.index
  change 2 * d.radius ≤ d.root at hh
  linarith [d.radius_pos]

/-- One explicit approximation error controls both the measured coordinates
and the actual radial quadratic error. -/
def error (d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M) : ℝ :=
  d.approximationError +
    2 * (((5 / 3 : ℝ) * (1024 : ℝ) ^ n) *
      (annularPoincareConstant K n * B / (3 / 4 * euclideanUnitVolume n) * d.totalSource)) +
    2 * (d.approximationError * (2 * (1 / 1024 : ℝ) + d.approximationError) / 2) ^ 2

theorem approximationError_le (hB : 0 ≤ B)
    (d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M) :
    d.approximationError ≤ d.error := by
  have hP := annularPoincareConstant_pos K n
  have hV := euclideanUnitVolume_pos n
  have hT := d.totalSource_nonneg
  have hterm : 0 ≤ 2 * (((5 / 3 : ℝ) * (1024 : ℝ) ^ n) *
      (annularPoincareConstant K n * B / (3 / 4 * euclideanUnitVolume n) * d.totalSource)) := by
    positivity
  dsimp only [error]
  linarith [sq_nonneg (d.approximationError * (2 * (1 / 1024 : ℝ) + d.approximationError) / 2)]

theorem error_pos (hB : 0 ≤ B)
    (d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M) :
    0 < d.error := d.approximationError_pos.trans_le (d.approximationError_le hB)

/-- The actual radial quadratic estimate on the outer projection ball. -/
theorem quadratic_error
    (hn : 2 ≤ n) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M) :
    ((hausdorff n X).real (ball d.center ((1 / 1024) * d.radius)))⁻¹ *
      (∫ x in ball d.center ((1 / 1024) * d.radius),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic
          ((d.radius ^ 2)⁻¹ • d.secondReplacement.replacement d.index) x -
            ‖d.coordinateValues x‖ ^ 2 / 2) ^ 2 ∂hausdorff n X) ≤ d.error := by
  let Ccoord : ℝ≥0 := ⟨1 / 1024 + d.approximationError, by
    linarith [d.approximationError_pos]⟩
  let u := radiusScaledColumns (hausdorff n X) hX.quadratic d.radius d.coordinates
  have hb (j : Fin n) : ∀ᵐ x ∂(hausdorff n X).restrict
      (ball d.center ((1 / 1024) * d.radius)),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) x| ≤ Ccoord := by
    filter_upwards [d.representative j, ae_restrict_mem measurableSet_ball] with x hx hball
    change SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) x = _ at hx
    rw [hx]
    have hnorm := (d.measured.metric.centered_norm_error d.radius_pos
      (by norm_num) d.centered hball.le).2
    exact (show |d.coordinateValues x j| ≤ ‖d.coordinateValues x‖ by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (d.coordinateValues x) j).trans hnorm
  let w := fun j => boundedLocalVersion (hausdorff n X) hX.quadratic (u j) Ccoord
  have hw (j : Fin n) : SobolevSpace.toLp (hausdorff n X) hX.quadratic (w j) =ᵐ[
      (hausdorff n X).restrict (ball d.center ((1 / 1024) * d.radius))]
      fun x => d.coordinateValues x j :=
    (boundedLocalVersion_eq (hausdorff n X) hX.quadratic (u j) Ccoord (hb j)).trans
      (d.representative j)
  have hh := actual_poisson_small_ball_quadratic_error hX hn d.secondReplacement
    hκ hB d.totalSource_nonneg d.approximationError_pos.le
    (by norm_num : (0 : ℝ) < 1 / 1024) (by norm_num : (1 / 1024 : ℝ) ≤ 1 / 4)
    d.root_le_one (euclideanUnitVolume_pos n) d.volume d.summable d.totalBudget d.index
    w Ccoord d.coordinateValues
    (fun j => boundedLocalVersion_bound (hausdorff n X) hX.quadratic (u j) Ccoord)
    hw d.measured.metric d.centered
  have hpow : ((1 / 1024 : ℝ)⁻¹) ^ n = (1024 : ℝ) ^ n := by norm_num
  rw [hpow] at hh
  change _ ≤ d.error
  exact hh.trans (by dsimp only [error]; linarith [d.approximationError_pos])

/-- The exact orthogonal residual norm of the actual two-center target. -/
def projectionNorm (d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M) : ℝ :=
  ‖normalizeLocalL2 (hausdorff n X) (ball d.center ((1 / 2048) * d.radius))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (affineResidual (hausdorff n X) hX.quadratic
      (radiusScaledColumns (hausdorff n X) hX.quadratic d.radius d.coordinates)
      (ball d.center ((1 / 2048) * d.radius)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball d.center ((1 / 2048) * d.radius))
        ((d.radius ^ 2)⁻¹ • (d.secondReplacement.replacement d.index - d.firstReplacement.replacement d.index))))‖

end ActualProjectionConfiguration
end RegularPointCoordinates

end

end OAI
