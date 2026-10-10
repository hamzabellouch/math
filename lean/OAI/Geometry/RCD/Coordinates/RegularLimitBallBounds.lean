import OAI.Geometry.RCD.Coordinates.RegularMovingVolumeRatio
import OAI.Geometry.RCD.Metric.PointedBallSandwich
import OAI.Geometry.RCD.Sobolev.WeakBallMassBounds

namespace OAI

/-! # Exact-volume bounds for the original laws in a regular metric limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {K : ℝ} {n : ℕ}

theorem NoncollapsedRCD.regular_limit_ball_bounds
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {o : X} (ho : IsRegular n o)
    {q z : Y} {S a t b : ℝ} (hS : 0 < S) (ha : 0 < a)
    (hat : a < t) (htb : t < b) (hroom : dist z q+b < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure Y}
    (hlim : Tendsto (fun k => metricBallLaw (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q)) :
    (a/S)^n ≤ (Q : Measure Y).real (closedBall z t) ∧
      (Q : Measure Y).real (ball z t) ≤ (b/S)^n := by
  let T := (dist z q+S-b)/2
  have hzT : dist z q < T := by dsimp only [T]; linarith
  have hTS : T < S := by dsimp only [T]; linarith [dist_nonneg (x := z) (y := q)]
  have haT : a+T ≤ S := by dsimp only [T]; linarith
  obtain ⟨x,hx,hxz⟩ := pointed_bounded_lift p r ε V hr hε hV hTS hzT
  have hxo : Tendsto x atTop (𝓝 o) := by
    apply hp.congr_dist
    have hsmall : Tendsto (fun k => T*r k) atTop (𝓝 0) := by
      simpa only [mul_zero] using hr0.const_mul T
    apply squeeze_zero (fun _ => dist_nonneg) _ hsmall
    intro k
    simpa only [dist_comm] using hx k
  have hsand := pointed_ball_sandwich_eventually p x r ε V hr hε hV hx hxz
    hTS.le haT hat htb
  have hpos k : 0 < (hausdorff n X).real (ball (p k) (S*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hfin k)
  constructor
  · apply weak_closed_mass_ge_of_tendsto hlim isClosed_closedBall
      (hX.regular_moving_volume_ratio hn ho p x r hp hxo hr hr0 hS ha)
    filter_upwards [hsand] with k hk
    rw [metricBallLaw_real _ _ _ _ _ _ (hpos k) (hVm k) measurableSet_closedBall,
      div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hpos k).le)
    apply measureReal_mono _ (hX.finiteOnBounded _ (isBounded_ball.subset inter_subset_right)).ne
    intro y hy
    exact ⟨ball_subset_closedBall (hk.1 hy).1,(hk.1 hy).2⟩
  · apply weak_open_mass_le_of_tendsto hlim isOpen_ball
      (hX.regular_moving_volume_ratio hn ho p x r hp hxo hr hr0 hS (ha.trans (hat.trans htb)))
    filter_upwards [hsand] with k hk
    rw [metricBallLaw_real _ _ _ _ _ _ (hpos k) (hVm k) measurableSet_ball,
      div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hpos k).le)
    apply measureReal_mono _ (hX.finiteOnBounded _ isBounded_ball).ne
    rintro y ⟨hy,hyS⟩
    exact hk.2 ⟨ball_subset_closedBall hy,hyS⟩

end RegularPointCoordinates

end

end OAI
