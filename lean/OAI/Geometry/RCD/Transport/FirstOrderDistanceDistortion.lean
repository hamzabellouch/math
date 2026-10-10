import OAI.Geometry.RCD.Harmonic.FirstOrderDistanceDefect
import OAI.Geometry.RCD.Coordinates.FirstOrderCoordinateDistance

namespace OAI

/-! # Two-sided metric distortion for the actual first-order coordinates -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_distance_distortion {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p x y : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (hx : ∀ k, dist (x k) (p k)≤r k/48) (hy : ∀ k, dist (y k) (p k)≤r k/48) :
    Tendsto (fun k => |dist (v k (x k)) (v k (y k))/r k-
      dist (x k) (y k)/r k|) atTop (𝓝 0) := by
  have hl := hX.first_order_distance_defect hn hK p x y r ε hr hr0 hcurv hε hε1 hε0 u v hsplit hx hy
  have hu := hX.first_order_coordinate_distance hn hK p x y r ε hr hr0 hcurv hε hε1 hε0 u v hsplit hx hy
  have hid (a b : ℝ) : |a-b|=max 0 (a-b)+max 0 (b-a) := by
    by_cases hab : b≤a
    · rw [abs_of_nonneg (sub_nonneg.mpr hab),max_eq_right (by linarith : 0≤a-b),
        max_eq_left (by linarith : b-a≤0),add_zero]
    · rw [abs_of_nonpos (by linarith : a-b≤0),max_eq_left (by linarith : a-b≤0),
        max_eq_right (by linarith : 0≤b-a),zero_add]
      ring
  simpa only [hid,add_zero] using hu.add hl

end RegularPointCoordinates

end

end OAI
