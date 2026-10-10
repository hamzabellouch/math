import OAI.Geometry.RCD.Metric.InwardDistance

namespace OAI

/-! # Radial midpoint rigidity and distance along a minimizing path

The nonnegative quadratic midpoint defect has zero integral for an
optimal coupling to a radial midpoint. Its zero set consists precisely
of metric midpoints on rays towards the pole.
-/

open Set Metric

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

theorem radial_midpoint_defect_nonneg (p x y : X) :
    0 ≤ 2 * dist x y ^ 2 + 2 * dist y p ^ 2 - dist x p ^ 2 := by
  have ht := dist_triangle x y p
  have ha := dist_nonneg (x := x) (y := p)
  have hb := dist_nonneg (x := x) (y := y)
  have hc := dist_nonneg (x := y) (y := p)
  nlinarith [sq_nonneg (dist x y - dist y p)]

theorem radial_midpoint_of_defect_zero {p x y : X}
    (hz : 2 * dist x y ^ 2 + 2 * dist y p ^ 2 - dist x p ^ 2 = 0) :
    dist x y = dist y p ∧ dist x p = dist x y + dist y p := by
  have ht := dist_triangle x y p
  have ha := dist_nonneg (x := x) (y := p)
  have hb := dist_nonneg (x := x) (y := y)
  have hc := dist_nonneg (x := y) (y := p)
  have he : dist x y = dist y p := by
    nlinarith [sq_nonneg (dist x y - dist y p)]
  refine ⟨he, ?_⟩
  nlinarith

theorem IsGeodesic.radial_distance {γ : C(Time, X)} (hγ : IsGeodesic γ)
    {p : X} (hradial : dist (γ 0) p = dist (γ 0) (γ 1) + dist (γ 1) p)
    (t : Time) :
    dist (γ t) p = dist (γ 0) p - (t : ℝ) * dist (γ 0) (γ 1) := by
  have hfirst : dist (γ 0) (γ t) = (t : ℝ) * dist (γ 0) (γ 1) := by
    rw [hγ]
    change |0 - (t : ℝ)| * dist (γ 0) (γ 1) = _
    rw [zero_sub, abs_neg, abs_of_nonneg t.2.1]
  have hlast : dist (γ t) (γ 1) = (1 - (t : ℝ)) * dist (γ 0) (γ 1) := by
    rw [hγ]
    change |(t : ℝ) - 1| * dist (γ 0) (γ 1) = _
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr t.2.2)]
  have hlo := dist_triangle (γ 0) (γ t) p
  have hhi := dist_triangle (γ t) (γ 1) p
  rw [hfirst] at hlo
  rw [hlast] at hhi
  linarith

theorem IsGeodesic.inwardDistance_increment {γ : C(Time, X)} (hγ : IsGeodesic γ)
    {p : X} {R : ℝ} (hR : dist (γ 0) p < R)
    (hradial : dist (γ 0) p = dist (γ 0) (γ 1) + dist (γ 1) p)
    (t : Time) :
    |inwardDistance p R (γ t) - inwardDistance p R (γ 0)| =
      (t : ℝ) * dist (γ 0) (γ 1) := by
  have hd := hγ.radial_distance hradial t
  have ht : 0 ≤ (t : ℝ) * dist (γ 0) (γ 1) := mul_nonneg t.2.1 dist_nonneg
  have hin : dist p (γ t) < R := by rw [dist_comm, hd]; linarith
  have hin0 : dist p (γ 0) < R := by simpa only [dist_comm] using hR
  rw [inwardDistance, inwardDistance, max_eq_left (sub_nonneg.mpr hin.le),
    max_eq_left (sub_nonneg.mpr hin0.le), dist_comm p (γ t), dist_comm p (γ 0), hd]
  have he : R - (dist (γ 0) p - (t : ℝ) * dist (γ 0) (γ 1)) -
      (R - dist (γ 0) p) = (t : ℝ) * dist (γ 0) (γ 1) := by ring
  rw [he, abs_of_nonneg ht]

end RegularPointCoordinates

end OAI
