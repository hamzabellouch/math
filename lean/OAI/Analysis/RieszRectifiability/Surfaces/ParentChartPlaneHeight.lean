import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.NeighborProjectionEstimates

namespace OAI

/-!
# Transferring parent-chart height bounds

For adjacent cell scales, neighboring-plane projection estimates transfer a height bound
relative to the parent plane to a quantitative bound relative to the child plane.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem parent_chart_plane_height_transfer {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (i q : SupportCellDescendant μ R hR k z)
    (hscale : q.radius = 64 * i.radius)
    (hnear : dist i.center q.center ≤ 2 * q.radius)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1024)
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (hSi : bilateralPlaneError μ i.center (1024 * i.radius) S < ε)
    (hWq : bilateralPlaneError μ q.center (1024 * q.radius) W < ε)
    (x : Ambient d) (hx : x ∈ closedBall q.center (3 * q.radius))
    (hheight : infDist x (W : Set (Ambient d)) ≤ (262144 * ε) * q.radius) :
    infDist x (S : Set (Ambient d)) ≤ (524288 * ε) * q.radius := by
  let : Nonempty S := hS.1.to_subtype
  let : Nonempty W := hW.1.to_subtype
  have hri := i.radius_pos
  have hrq := q.radius_pos
  have hsmall : i.radius ≤ q.radius := by rw [hscale]; linarith
  have hlarge : q.radius ≤ 64 * i.radius := hscale.le
  have hneighbor : dist i.center q.center ≤ 128 * q.radius := by linarith
  have hop := neighbor_cell_projection_operator_norm_le μ R hR k z i q
    hsmall hlarge hneighbor ε hε hεsmall S W hS hW hSi hWq
  have hScenter := (bilateralPlaneError_lt_pointwise μ ⟨i.center, i.center_mem_support⟩
    i.center (1024 * i.radius) ε (by positivity) S hS hSi).1 i.center
      (mem_ball_self (by positivity)) i.center_mem_support
  have hWcenter := (bilateralPlaneError_lt_pointwise μ ⟨i.center, i.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) W hW hWq).1 i.center
      (by change dist i.center q.center < 1024 * q.radius; linarith) i.center_mem_support
  have hdx : dist x i.center ≤ 5 * q.radius := by
    have ht := dist_triangle x q.center i.center
    rw [dist_comm q.center i.center] at ht
    have hx' : dist x q.center ≤ 3 * q.radius := hx
    linarith
  have hpair := affine_projection_pair_dist_bound S W i.center x (2048 * ε) hop
  have hm := mul_le_mul_of_nonneg_left hdx (show 0 ≤ 2048 * ε by positivity)
  have ht := dist_triangle (orthogonalProjection S x : Ambient d)
    (orthogonalProjection W x : Ambient d) x
  rw [dist_comm (orthogonalProjection S x : Ambient d) x,
    dist_orthogonalProjection_eq_infDist S x,
    dist_comm (orthogonalProjection W x : Ambient d) x,
    dist_orthogonalProjection_eq_infDist W x] at ht
  have hscaleError := mul_le_mul_of_nonneg_left hsmall hε.le
  nlinarith [mul_pos hε hrq]

end

end RieszRectifiability

end OAI
