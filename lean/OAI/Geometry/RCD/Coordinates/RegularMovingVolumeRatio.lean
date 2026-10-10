import OAI.Geometry.RCD.Coordinates.RegularMovingVolume

namespace OAI

/-! # Exact relative volume limits at moving regular centers -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ}

theorem NoncollapsedRCD.regular_moving_volume_ratio
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {o : X} (ho : IsRegular n o)
    (p x : ℕ → X) (r : ℕ → ℝ) (hp : Tendsto p atTop (𝓝 o))
    (hx : Tendsto x atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {S t : ℝ} (hS : 0 < S) (ht : 0 < t) :
    Tendsto (fun k => (hausdorff n X).real (ball (x k) (t*r k)) /
      (hausdorff n X).real (ball (p k) (S*r k))) atTop (𝓝 ((t/S)^n)) := by
  have hnum := hX.regular_moving_volume_limit hn ho x (fun k => t*r k) hx
    (fun k => mul_pos ht (hr k)) (by simpa using hr0.const_mul t)
  have hden := hX.regular_moving_volume_limit hn ho p (fun k => S*r k) hp
    (fun k => mul_pos hS (hr k)) (by simpa using hr0.const_mul S)
  have hω := euclideanUnitVolume_pos n
  have hlim := (hnum.div hden hω.ne').mul_const ((t/S)^n)
  simp only [div_self hω.ne',one_mul] at hlim
  convert hlim using 1
  ext k
  have hb : (hausdorff n X).real (ball (p k) (S*r k)) ≠ 0 :=
    (ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne).ne'
  change (hausdorff n X).real (ball (x k) (t*r k)) /
      (hausdorff n X).real (ball (p k) (S*r k)) =
    ((hausdorff n X).real (ball (x k) (t*r k))/(t*r k)^n) /
      ((hausdorff n X).real (ball (p k) (S*r k))/(S*r k)^n) * (t/S)^n
  rw [mul_pow,mul_pow,div_pow]
  field_simp [hb, hS.ne', ht.ne', (hr k).ne']

end RegularPointCoordinates

end

end OAI
