import OAI.Geometry.RCD.Transport.MetricPreimageMidpointVolume
import OAI.Geometry.RCD.Transport.PointedLocalGeodesic

namespace OAI

/-! # Local midpoint volume control throughout the approximation ball

The endpoints can be near any interior target point. The radius condition
only keeps their short connecting geodesics inside the working region.
-/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem pointed_local_geodesic_radius {n : ℕ} {p : X} {r S ρ η ε : ℝ}
    (hr : 0 < r) (hρS : ρ ≤ S)
    {V : X → Euclidean n} (hV : IsPointedApproximation p 0 r S ε V)
    {γ : C(Time,X)} (hg : IsGeodesic γ)
    (h0 : dist (γ 0) p ≤ ρ*r) (h1 : dist (γ 1) p ≤ ρ*r)
    {z : Euclidean n} (hz0 : V (γ 0) ∈ closedBall z η)
    (hz1 : V (γ 1) ∈ closedBall z η) (t : Time) :
    dist (γ t) p ≤ (ρ+2*η+ε)*r := by
  have hsr := mul_le_mul_of_nonneg_right hρS hr.le
  have hd := (abs_le.mp (hV.2.1 _ _ (h0.trans hsr) (h1.trans hsr))).1
  have him := dist_triangle (V (γ 0)) z (V (γ 1))
  rw [dist_comm z (V (γ 1))] at him
  have hD : dist (γ 0) (γ 1) ≤ (2*η+ε)*r := by
    apply (div_le_iff₀ hr).mp
    change dist (V (γ 0)) z ≤ η at hz0
    change dist (V (γ 1)) z ≤ η at hz1
    linarith
  have ht : dist (γ t) (γ 0) ≤ dist (γ 0) (γ 1) := by
    rw [hg t 0]
    change |(t:ℝ)-0| * dist (γ 0) (γ 1) ≤ dist (γ 0) (γ 1)
    simp only [sub_zero,abs_of_nonneg t.2.1]
    exact mul_le_of_le_one_left dist_nonneg t.2.2
  have hb := dist_triangle (γ t) (γ 0) p
  nlinarith

theorem NoncollapsedRCD.metric_local_midpoint_volume {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {p : X} {r S ρ η ε a b : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hρS : ρ ≤ S) (hε : 0 ≤ ε)
    (hroom : ρ+2*η+ε ≤ S)
    (V : X → Euclidean n) (hVm : Measurable V)
    (hV : IsPointedApproximation p 0 r S ε V) (x y z : Euclidean n)
    (hx : closedBall x a ⊆ closedBall z η) (hy : closedBall y b ⊆ closedBall z η)
    (hA0 : hausdorff n X (V ⁻¹' closedBall x a ∩ closedBall p (ρ*r)) ≠ 0)
    (hB0 : hausdorff n X (V ⁻¹' closedBall y b ∩ closedBall p (ρ*r)) ≠ 0) :
    let A := V ⁻¹' closedBall x a ∩ closedBall p (ρ*r)
    let B := V ⁻¹' closedBall y b ∩ closedBall p (ρ*r)
    let C := V ⁻¹' closedBall ((1/2:ℝ) • (x+y))
      ((a+b)/2+Real.sqrt (2*(ε*(4*ρ+ε)))) ∩ closedBall p ((ρ+2*η+ε)*r)
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
    (uniformOn_finiteSecondMoment μ A hA hA0 hAfin p (ρ*r) (fun _ hu => hu.2))
    (uniformOn_finiteSecondMoment μ B hB hB0 hBfin p (ρ*r) (fun _ hu => hu.2)) (2*ρ*r)
  · intro u hu v hv
    have hd := dist_triangle u p v
    rw [dist_comm p v] at hd
    have hu' : dist u p ≤ ρ*r := hu.2
    have hv' : dist v p ≤ ρ*r := hv.2
    linarith
  · intro γ hg h0 h1
    have hp0 : dist (γ 0) p ≤ ρ*r := h0.2
    have hp1 : dist (γ 1) p ≤ ρ*r := h1.2
    have hpoints := pointed_local_geodesic_radius hr hρS hV hg hp0 hp1 (hx h0.1) (hy h1.1)
    refine ⟨pointed_midpoint_balls_within hr hρ hε hV hg hp0 hp1
      (fun t => (hpoints t).trans (mul_le_mul_of_nonneg_right hroom hr.le)) h0.1 h1.1,
      hpoints midpointTime⟩

end RegularPointCoordinates

end

end OAI
