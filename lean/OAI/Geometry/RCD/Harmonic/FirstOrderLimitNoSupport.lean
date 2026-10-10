import OAI.Geometry.RCD.Harmonic.FirstOrderMovingNoSupport
import OAI.Geometry.RCD.Metric.LimitSupportTransfer

namespace OAI

/-! # No supporting boundary for the actual coordinate limit -/

open Set Filter Metric MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [MetricSpace Y]

theorem NoncollapsedRCD.first_order_limit_no_support {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε δ : ℕ → ℝ) (V : ℕ → X → Y) (q : Y)
    (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(80*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (δ k) (V k))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hs : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (u k) (v k))
    (F : Y → Euclidean n) (hF : Continuous F)
    (hvalues : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p k)≤5*r k →
      dist ((r k)⁻¹ • (v k x-v k (p k))) (F (V k x))≤η)
    {y : Y} (hy : dist y q<1/256) (a : Euclidean n) (ha : ‖a‖=1)
    (hsupport : ∀ x∈closedBall q (1/256), ⟪F x-F y,a⟫_ℝ≤0) : False := by
  obtain ⟨z,hz,hVy⟩ := pointed_metric_interior_lift p r δ V hr hδ0 hV
    (by norm_num : (1/128:ℝ)<5) (hy.trans (by norm_num))
  simp only [one_div_mul_eq_div] at hz
  obtain ⟨c,hc,hc1,hinner⟩ := pointed_inner_neighborhood p z r δ V hr hδ0 hV hz hVy hy
  apply hX.first_order_moving_no_support hn hK p z r ε hr hr0 hcurv hε hε1 hε0
    u v hs hz hc hc1 a ha
  exact limit_support_transfer p z r V v F hr hF hVy hvalues hinner a ha hsupport

end RegularPointCoordinates

end

end OAI
