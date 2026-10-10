import OAI.Geometry.RCD.Transport.MidpointSupportVolume
import OAI.Geometry.RCD.Transport.PointedMidpointBalls
import OAI.Geometry.RCD.Coordinates.Proper

namespace OAI

/-! # Midpoint volume control for preimages under metric approximation maps -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_preimage_midpoint_volume {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {p : X} {r S ρ ε a b : ℝ} (hr : 0<r) (hρ : 0≤ρ) (hε : 0≤ε) (hroom : 3*ρ≤S)
    (V : X → Euclidean n) (hVm : Measurable V)
    (hV : IsPointedApproximation p 0 r S ε V) (x y : Euclidean n)
    (hA0 : hausdorff n X (V ⁻¹' closedBall x a ∩ closedBall p (ρ*r)) ≠ 0)
    (hB0 : hausdorff n X (V ⁻¹' closedBall y b ∩ closedBall p (ρ*r)) ≠ 0) :
    let A := V ⁻¹' closedBall x a ∩ closedBall p (ρ*r)
    let B := V ⁻¹' closedBall y b ∩ closedBall p (ρ*r)
    let C := V ⁻¹' closedBall ((1/2:ℝ) • (x+y))
      ((a+b)/2+Real.sqrt (2*(ε*(4*ρ+ε)))) ∩ closedBall p (3*ρ*r)
    midpointFloor K n (2*ρ*r)*
      ((hausdorff n X A)^(1/(n:ℝ))+(hausdorff n X B)^(1/(n:ℝ))) ≤
        (hausdorff n X C)^(1/(n:ℝ)) := by
  let μ := hausdorff n X
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  dsimp only
  let A := V ⁻¹' closedBall x a ∩ closedBall p (ρ*r)
  let B := V ⁻¹' closedBall y b ∩ closedBall p (ρ*r)
  have hA : MeasurableSet A := (hVm measurableSet_closedBall).inter measurableSet_closedBall
  have hB : MeasurableSet B := (hVm measurableSet_closedBall).inter measurableSet_closedBall
  have hAfin : μ A ≠ ∞ := (hX.finiteOnBounded A (isBounded_closedBall.subset inter_subset_right)).ne
  have hBfin : μ B ≠ ∞ := (hX.finiteOnBounded B (isBounded_closedBall.subset inter_subset_right)).ne
  apply hX.cd.midpoint_support_volume_bound μ hn A B _ hA hB
    ((hVm measurableSet_closedBall).inter measurableSet_closedBall) hA0 hAfin hB0 hBfin
    (uniformOn_finiteSecondMoment μ A hA hA0 hAfin p (ρ*r) (fun _ hx => hx.2))
    (uniformOn_finiteSecondMoment μ B hB hB0 hBfin p (ρ*r) (fun _ hx => hx.2)) (2*ρ*r)
  · intro u hu v hv
    have hd := dist_triangle u p v
    rw [dist_comm p v] at hd
    have hu' : dist u p≤ρ*r := hu.2
    have hv' : dist v p≤ρ*r := hv.2
    linarith
  · intro γ hg h0 h1
    have hp0 : dist (γ 0) p≤ρ*r := h0.2
    have hp1 : dist (γ 1) p≤ρ*r := h1.2
    refine ⟨pointed_midpoint_balls hr hρ hε hroom hV hg hp0 hp1 h0.1 h1.1,?_⟩
    have hd := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm p (γ 1)] at hd
    have hm := dist_triangle (γ midpointTime) (γ 0) p
    rw [hg midpointTime 0] at hm
    norm_num [midpointTime] at hm
    change dist (γ midpointTime) p≤3*ρ*r
    nlinarith [mul_nonneg hρ hr.le]

end RegularPointCoordinates

end

end OAI
