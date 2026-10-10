import OAI.Geometry.RCD.Metric.VolumeDensity

namespace OAI

/-! # Ball volumes vanish at shrinking radii -/

open Set Metric MeasureTheory Filter
open scoped Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.ball_volume_tendsto_zero {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
    {s : ℕ → ℝ} (hs : ∀ i, 0 < s i) (hszero : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun i => (hausdorff n X).real (ball p (s i))) atTop (𝓝 0) := by
  have hn0 : n ≠ 0 := by omega
  have hc : Continuous (fun r : ℝ => (euclideanUnitVolume n *
      Real.exp (2 * r * Real.sqrt (|K| / ((n : ℝ) - 1))) ^ n) * r ^ n) := by fun_prop
  have hlim : Tendsto (fun i => (euclideanUnitVolume n *
      Real.exp (2 * s i * Real.sqrt (|K| / ((n : ℝ) - 1))) ^ n) * s i ^ n)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, Real.exp_zero, one_pow, mul_one, zero_pow hn0,
      Function.comp_def] using hc.continuousAt.tendsto.comp hszero
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun i => hX.normalized_ball_volume_upper hn p (hs i)) hlim

end RegularPointCoordinates

end OAI
