import OAI.Geometry.RCD.Coordinates.RegularLimitQuadraticMidpoint
import OAI.Geometry.RCD.Transport.LocalQuadraticMidpointGeometry

namespace OAI

/-! # Local midpoint geometry constructed from the original RCD sequence -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [MetricSpace Y] [ProperSpace Y] {K : ℝ} {n : ℕ}
  (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]

include hX in
theorem regular_limit_midpoint_geometry (hn : 2 ≤ n) (hK : K ≤ 0)
    {o : X} (ho : IsRegular n o) {q : Y}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K * (4 * r k)^2)
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k)) :
    Nonempty (LocalQuadraticMidpointGeometry q) := by
  classical
  have hex (x y : ball q (1/2:ℝ)) := hX.regular_limit_quadratic_midpoint hn hK ho
    p r ε V hp hr hr0 hε hcurv hV x.property y.property
  choose c hc hleft hright hquad using hex
  exact ⟨{
    mid := fun x y => ⟨c x y,hc x y⟩
    left := hleft
    right := hright
    quadratic := hquad }⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
