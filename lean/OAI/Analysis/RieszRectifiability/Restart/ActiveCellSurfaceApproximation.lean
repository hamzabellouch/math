import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceCharts

namespace OAI

/-!
# Bilateral approximation by active-cell surfaces

Exact tangential chart coordinates and the reference-plane height bound locate surface points
near support points. Conversely, surface points in the inner ball remain close to the support
by projecting onto the bilaterally approximating plane. Both estimates retain the explicit
error constant at the cell radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (q : SupportCellDescendant μ R hR k z)
  (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
  (ε : ℝ)
  (hfit : bilateralPlaneError μ q.center (1024 * q.radius) S < ε)
  (A : Set (Ambient d)) (hchart : HasActiveCellSurfaceChart q S ε A)

include hS hfit hchart

theorem active_cell_support_point_near_surface (x : Ambient d) (hx : x ∈ μ.support)
    (hnear : dist x q.center ≤ 2 * q.radius) :
    ∃ y ∈ A, dist x y ≤ (263168 * ε) * q.radius := by
  obtain ⟨g, _, _, hgCoords, _⟩ := hchart
  let P := S.direction
  have hr := q.radius_pos
  have hu : P.orthogonalProjectionOnto x ∈ closedBall (P.orthogonalProjectionOnto q.center)
      ((5 / 2 : ℝ) * q.radius) := by
    have hp := P.norm_starProjection_apply_le (x - q.center)
    rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
    change dist (P.starProjection x) (P.starProjection q.center) ≤ (5 / 2 : ℝ) * q.radius
    linarith
  let u : closedBall (P.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) :=
    ⟨P.orthogonalProjectionOnto x, hu⟩
  refine ⟨g u, (hgCoords u).1, ?_⟩
  have hc : P.starProjection (g u) = P.starProjection x :=
    congrArg (fun v : P => (v : Ambient d)) (hgCoords u).2.1
  have ht := dist_le_projection_add_plane_distances S hS.1 x (g u)
  change dist x (g u) ≤ dist (P.starProjection x) (P.starProjection (g u)) +
    infDist x (S : Set (Ambient d)) + infDist (g u) (S : Set (Ambient d)) at ht
  rw [hc, dist_self, zero_add] at ht
  have hxheight := (bilateralPlaneError_lt_pointwise μ ⟨q.center, q.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) S hS hfit).1 x
      (by change dist x q.center < 1024 * q.radius; linarith) hx
  have hyheight := (hgCoords u).2.2.1
  nlinarith

theorem active_cell_surface_point_near_support (hεsmall : ε ≤ 1 / 524288)
    (x : Ambient d) (hx : x ∈ A)
    (hnear : x ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius)) :
    infDist x μ.support ≤ (263168 * ε) * q.radius := by
  let : Nonempty S := hS.1.to_subtype
  let p := nonemptyAffineProjection S hS.1 x
  have hr := q.radius_pos
  have hheight := HasActiveCellSurfaceChart.height_on_inner_ball q S ε A hchart x hx hnear
  have hdist : dist p x ≤ (262144 * ε) * q.radius := by
    rw [nonemptyAffineProjection_dist_self]
    exact hheight
  have hδ := mul_le_mul_of_nonneg_right hεsmall hr.le
  have hpnear : p ∈ ball q.center (1024 * q.radius) := by
    have ht := dist_triangle p x q.center
    have hx' : dist x q.center ≤ (9 / 4 : ℝ) * q.radius := hnear
    change dist p q.center < 1024 * q.radius
    nlinarith
  have hpS : p ∈ S := orthogonalProjection_mem x
  have hpheight := (bilateralPlaneError_lt_pointwise μ ⟨q.center, q.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) S hS hfit).2 p hpnear hpS
  have ht : infDist x μ.support ≤ infDist p μ.support + dist x p := infDist_le_infDist_add_dist
  rw [dist_comm x p] at ht
  nlinarith

end

end RieszRectifiability

end OAI
