import OAI.Geometry.RCD.Transport.PointedMidpointSets
import OAI.Geometry.RCD.Transport.MetricLocalMidpointVolume
import OAI.Geometry.RCD.Transport.MidpointMinMass

namespace OAI

/-! # The actual CD midpoint inequality for arbitrary bounded target sets -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_set_midpoint_volume {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {p : X} {r S ρ η ε : ℝ} (hr : 0 < r) (hρ : 0 ≤ ρ) (hρS : ρ ≤ S)
    (he : 0 ≤ ε) (hroom : ρ+2*η+ε ≤ S)
    (V : X → Euclidean n) (hVm : Measurable V) (hV : IsPointedApproximation p 0 r S ε V)
    {A B : Set (Euclidean n)} (hA : MeasurableSet A) (hB : MeasurableSet B) (z : Euclidean n)
    (hAsub : A ⊆ closedBall z η) (hBsub : B ⊆ closedBall z η)
    (hA0 : hausdorff n X (V ⁻¹' A ∩ closedBall p (ρ*r)) ≠ 0)
    (hB0 : hausdorff n X (V ⁻¹' B ∩ closedBall p (ρ*r)) ≠ 0) :
    let P := V ⁻¹' A ∩ closedBall p (ρ*r)
    let Q := V ⁻¹' B ∩ closedBall p (ρ*r)
    let C := V ⁻¹' cthickening (Real.sqrt (2*(ε*(4*ρ+ε)))) (midpointSet A B) ∩
      closedBall p ((ρ+2*η+ε)*r)
    (2*midpointFloor K n (2*ρ*r))^n*min (hausdorff n X P) (hausdorff n X Q) ≤ hausdorff n X C := by
  let μ := hausdorff n X
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  dsimp only
  let P := V ⁻¹' A ∩ closedBall p (ρ*r)
  let Q := V ⁻¹' B ∩ closedBall p (ρ*r)
  have hP : MeasurableSet P := (hVm hA).inter measurableSet_closedBall
  have hQ : MeasurableSet Q := (hVm hB).inter measurableSet_closedBall
  have hPfin : μ P ≠ ∞ := (hX.finiteOnBounded P (isBounded_closedBall.subset inter_subset_right)).ne
  have hQfin : μ Q ≠ ∞ := (hX.finiteOnBounded Q (isBounded_closedBall.subset inter_subset_right)).ne
  apply midpoint_root_bound_to_min_mass (by omega : 0 < n)
  apply hX.cd.midpoint_support_volume_bound μ hn P Q _ hP hQ
    ((hVm isClosed_cthickening.measurableSet).inter measurableSet_closedBall)
    hA0 hPfin hB0 hQfin
    (uniformOn_finiteSecondMoment μ P hP hA0 hPfin p (ρ*r) (fun _ hu => hu.2))
    (uniformOn_finiteSecondMoment μ Q hQ hB0 hQfin p (ρ*r) (fun _ hu => hu.2)) (2*ρ*r)
  · intro x hx y hy
    have hd := dist_triangle x p y
    rw [dist_comm p y] at hd
    have hx' : dist x p ≤ ρ*r := hx.2
    have hy' : dist y p ≤ ρ*r := hy.2
    linarith only [hd,hx',hy']
  · intro γ hg h0 h1
    have hp0 : dist (γ 0) p ≤ ρ*r := h0.2
    have hp1 : dist (γ 1) p ≤ ρ*r := h1.2
    have hpoints := pointed_local_geodesic_radius hr hρS hV hg hp0 hp1
      (hAsub h0.1) (hBsub h1.1)
    exact ⟨pointed_midpoint_sets_within hr hρ he hV hg hp0 hp1
      (fun t => (hpoints t).trans (mul_le_mul_of_nonneg_right hroom hr.le)) h0.1 h1.1,
      hpoints midpointTime⟩

end RegularPointCoordinates

end

end OAI
