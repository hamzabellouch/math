import OAI.Geometry.RCD.Sobolev.WeightedGammaL2Continuity

namespace OAI

/-! # Joint limits of L²-weighted gradient pairings -/

open Filter MeasureTheory
open scoped NNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weightedGamma_joint_tendsto (w : SobolevSpace μ hQ)
    {ds : ℕ → Lp ℝ 2 μ} {d : Lp ℝ 2 μ}
    {us : ℕ → SobolevSpace μ hQ} {u : SobolevSpace μ hQ} (L : ℝ≥0)
    (hus : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (us k) x ≤ L)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    (hconv : Tendsto us atTop (𝓝 u)) (hd : Tendsto ds atTop (𝓝 d)) :
    Tendsto (fun k => weightedGamma μ hQ (ds k) (us k) w) atTop
      (𝓝 (weightedGamma μ hQ d u w)) := by
  have herr : Tendsto (fun k => weightedGamma μ hQ (ds k) (us k) w -
      weightedGamma μ hQ d (us k) w) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun k => (L : ℝ) * ‖ds k - d‖ * ‖SobolevSpace.minimalSlope μ hQ w‖)
    · intro k
      rw [Real.norm_eq_abs, ← weightedGamma_weight_difference μ hQ (ds k) d (us k) w L (hus k)]
      exact weightedGamma_le_of_bounded_gradient μ hQ (ds k - d) (us k) w L (hus k)
    · have hh := (((hd.sub (tendsto_const_nhds (x := d))).norm).const_mul (L : ℝ)).mul_const
        ‖SobolevSpace.minimalSlope μ hQ w‖
      simpa only [sub_self, norm_zero, mul_zero, zero_mul] using hh
  have hh := herr.add (weightedGamma_fixed_weight_tendsto μ hQ d w L hus hu hconv)
  simpa only [sub_add_cancel, zero_add] using hh

end RegularPointCoordinates

end OAI
