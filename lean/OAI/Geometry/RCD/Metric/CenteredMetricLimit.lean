import OAI.Geometry.RCD.Metric.MovingPointedLimitApproximation

namespace OAI

/-! # Centering passes through the prescribed metric maps -/

open Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

omit [MetricSpace X] in
theorem centered_metric_limit_zero {q : Y} (p : ℕ → X) (V : ℕ → X → Y)
    (ε : ℕ → ℝ) (u : ℕ → X → ℝ) (g : Y → ℝ)
    (hg : ContinuousAt g q) (hε : Tendsto ε atTop (𝓝 0))
    (hVp : ∀ k, dist (V k (p k)) q≤ε k) (hu : ∀ k, u k (p k)=0)
    (hconv : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, |u k (p k)-g (V k (p k))|<η) :
    g q=0 := by
  have hV : Tendsto (fun k => V k (p k)) atTop (𝓝 q) :=
    tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun _ => dist_nonneg) hVp hε)
  have hzero : Tendsto (fun k => g (V k (p k))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hconv η hη] with k hk
    simpa only [hu k,zero_sub,abs_neg,dist_zero_right,Real.norm_eq_abs] using hk
  exact tendsto_nhds_unique (hg.tendsto.comp hV) hzero

end RegularPointCoordinates

end

end OAI
