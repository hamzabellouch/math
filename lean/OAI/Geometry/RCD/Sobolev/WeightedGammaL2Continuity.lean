import OAI.Geometry.RCD.Metric.L2ClippingApproximation
import OAI.Geometry.RCD.Sobolev.WeightedGammaGradientBound
import OAI.Geometry.RCD.Sobolev.GammaL2Bound
import OAI.Geometry.RCD.Metric.UniformApproximationLimit

namespace OAI

/-! # L²-weight continuity with a uniform gradient bound

Clip the weight, pass the bounded-weight Sobolev limit, and control the
tail with the common gradient bound. The test needs only Sobolev regularity.
-/

open Filter MeasureTheory
open scoped NNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weightedGamma_weight_difference (a b : Lp ℝ 2 μ) (u w : SobolevSpace μ hQ)
    (L : ℝ≥0) (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L) :
    weightedGamma μ hQ (a - b : Lp ℝ 2 μ) u w =
      weightedGamma μ hQ a u w - weightedGamma μ hQ b u w := by
  have hΓ := localGamma_memLp_of_bounded_gradient μ hQ u w L hu
  simp only [weightedGamma_eq_L2_inner μ hQ u w hΓ, inner_sub_left]

theorem weightedGamma_fixed_weight_tendsto (d : Lp ℝ 2 μ) (w : SobolevSpace μ hQ)
    {us : ℕ → SobolevSpace μ hQ} {u : SobolevSpace μ hQ} (L : ℝ≥0)
    (hus : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (us k) x ≤ L)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    (hconv : Tendsto us atTop (𝓝 u)) :
    Tendsto (fun k => weightedGamma μ hQ d (us k) w) atTop (𝓝 (weightedGamma μ hQ d u w)) := by
  let ds (j : ℕ) := boundedL2Clip μ j d
  let e (j : ℕ) := (L : ℝ) * ‖d - ds j‖ * ‖SobolevSpace.minimalSlope μ hQ w‖
  apply tendsto_of_uniformly_close_sequences
    (a := fun j k => weightedGamma μ hQ (ds j) (us k) w)
    (b := fun j => weightedGamma μ hQ (ds j) u w) (e := e)
  · intro j
    have hb : ∀ᵐ x ∂μ, ‖ds j x‖ ≤ ((j : ℝ≥0) : ℝ) := by
      simpa only [Real.norm_eq_abs] using boundedL2Clip_abs_le μ j d
    exact ((((weightedGammaCLM μ hQ (Lp.aestronglyMeasurable (ds j)) hb).flip w).continuous.tendsto u).comp hconv)
  · have hd := ((tendsto_const_nhds (x := d)).sub (boundedL2Clip_tendsto μ d)).norm
    simpa only [sub_self, norm_zero, mul_zero, zero_mul, e, ds] using
      (hd.const_mul (L : ℝ)).mul_const ‖SobolevSpace.minimalSlope μ hQ w‖
  · intro j k
    rw [Real.dist_eq, ← weightedGamma_weight_difference μ hQ d (ds j) (us k) w L (hus k)]
    exact weightedGamma_le_of_bounded_gradient μ hQ (d - ds j) (us k) w L (hus k)
  · intro j
    rw [dist_comm, Real.dist_eq, ← weightedGamma_weight_difference μ hQ d (ds j) u w L hu]
    exact weightedGamma_le_of_bounded_gradient μ hQ (d - ds j) u w L hu

end RegularPointCoordinates

end OAI
