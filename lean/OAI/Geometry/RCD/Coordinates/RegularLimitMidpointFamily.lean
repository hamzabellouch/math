import OAI.Geometry.RCD.Coordinates.RegularPointedMidpoint
import OAI.Geometry.RCD.Metric.PointedBoundedLifts

namespace OAI

/-! # Simultaneous midpoint identities for countably many prescribed limit points -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [MetricSpace Y] [ProperSpace Y] {K : ℝ} {n : ℕ}
  (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]

include hX in
theorem regular_limit_midpoint_family (hn : 2 ≤ n) (hK : K ≤ 0)
    {o : X} (ho : IsRegular n o) {q a b : Y} (w : ℕ → Y)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K * (4 * r k)^2)
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k))
    (ha : dist a q < 1/2) (hb : dist b q < 1/2) (hw : ∀ i, dist (w i) q < 1) :
    ∃ c : Y, dist c q ≤ 4 ∧ dist a c = dist a b/2 ∧ dist c b = dist a b/2 ∧
      ∀ i, dist (w i) c^2 = (dist (w i) a^2+dist (w i) b^2)/2-dist a b^2/4 := by
  obtain ⟨x,hx,hVx⟩ := pointed_bounded_lift p r ε V hr hε hV (by norm_num) ha
  obtain ⟨y,hy,hVy⟩ := pointed_bounded_lift p r ε V hr hε hV (by norm_num) hb
  have hex i := pointed_bounded_lift p r ε V hr hε hV (by norm_num : (1:ℝ)<5) (hw i)
  choose z hz hVz using hex
  exact hX.regular_pointed_midpoint hn hK ho w p x y z r ε V hp hr hr0 hε hcurv hV
    (fun k => by simpa only [div_eq_mul_inv,one_mul,mul_comm] using hx k)
    (fun k => by simpa only [div_eq_mul_inv,one_mul,mul_comm] using hy k)
    (fun i k => by simpa only [one_mul] using hz i k) hVx hVy hVz

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
