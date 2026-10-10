import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-! # Restricting a pointed approximation to a smaller ball -/

open Metric

namespace RegularPointCoordinates

/-- Restriction costs a factor three in the approximation error because
the preimage supplied by density must be shown to lie in the smaller ball. -/
theorem IsPointedApproximation.restrict_radius {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {p : X} {q : Y} {r R S ε : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (hSR : S ≤ R) (hε : 0 ≤ ε)
    {f : X → Y} (hf : IsPointedApproximation p q r R ε f) :
    IsPointedApproximation p q r S (3 * ε) f := by
  have hlarge {x : X} (hx : dist x p ≤ S * r) : dist x p ≤ R * r :=
    hx.trans (mul_le_mul_of_nonneg_right hSR hr.le)
  have hpp : dist p p ≤ R * r := by
    simp only [dist_self]
    exact mul_nonneg (hS.trans hSR) hr.le
  refine ⟨hf.1.trans (by linarith), fun x y hx hy =>
    (hf.2.1 x y (hlarge hx) (hlarge hy)).trans (by linarith), ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hf.2.2 y (by linarith)
  refine ⟨x, ?_, hxy.trans (by linarith)⟩
  have hd := (abs_le.mp (hf.2.1 x p hx hpp)).1
  have ht := dist_triangle (f x) y (f p)
  have ht' := dist_triangle y q (f p)
  have hbase := hf.1
  rw [dist_comm (f p)] at hbase
  apply (div_le_iff₀ hr).mp
  linarith

end RegularPointCoordinates

end OAI
