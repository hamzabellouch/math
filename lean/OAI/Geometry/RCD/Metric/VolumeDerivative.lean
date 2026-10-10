import OAI.Geometry.RCD.Metric.AnnularDerivativeComparison

namespace OAI

/-! # The radial area-density inequality at every pair of derivative points -/

open Set Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.ball_annulus_real {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    (hausdorff n X).real (ball p R \ closedBall p r) =
      (hausdorff n X).real (ball p R) - (hausdorff n X).real (ball p r) := by
  rw [measureReal_sdiff (closedBall_subset_ball hrR) measurableSet_closedBall
    (hX.finiteOnBounded _ isBounded_ball).ne]
  have h := hX.closedBall_measure_eq_ball hn p hr
  exact congrArg (fun v : ℝ≥0∞ => (hausdorff n X).real (ball p R) - v.toReal) h

theorem NoncollapsedRCD.radial_derivative_comparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K < 0) (p : X)
    {x y vx vy : ℝ} (hx : 0 < x) (hxy : x < y)
    (hdx : HasDerivAt (fun r => (hausdorff n X).real (ball p r)) vx x)
    (hdy : HasDerivAt (fun r => (hausdorff n X).real (ball p r)) vy y) :
    let a := Real.sqrt (-K / ((n : ℝ) - 1))
    Real.sinh (x * a) ^ (n - 1) * vy ≤ Real.sinh (y * a) ^ (n - 1) * vx := by
  dsimp only
  let a := Real.sqrt (-K / ((n : ℝ) - 1))
  let w : ℝ → ℝ := fun r => Real.sinh (r * a) ^ (n - 1)
  let α := x / y
  have hy : 0 < y := hx.trans hxy
  have hα : 0 < α := div_pos hx hy
  have hα1 : α < 1 := (div_lt_one hy).mpr hxy
  have hαy : α * y = x := div_mul_cancel₀ x hy.ne'
  apply derivative_density_le_of_annular_comparison hα hdx hdy
    (show ContinuousAt w x by fun_prop) (show ContinuousAt w y by fun_prop)
  intro h hh
  have houter : α * (y + h) = x + α * h := by
    rw [mul_add, hαy]
  have hsmall : x < x + α * h := lt_add_of_pos_right _ (mul_pos hα hh)
  have hcomp := hX.annular_volume_ratio hn hK p hy (by linarith : y < y + h) hα hα1
  change (α * w (α * (y + h))) *
      (hausdorff n X).real (ball p (y + h) \ closedBall p y) ≤
    w (y + h) * (hausdorff n X).real
      (ball p (α * (y + h)) \ closedBall p (α * y)) at hcomp
  rw [houter, hαy, hX.ball_annulus_real hn p hy (by linarith),
    hX.ball_annulus_real hn p hx hsmall] at hcomp
  exact hcomp

end RegularPointCoordinates

end OAI
