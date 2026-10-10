import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.LocalPlaneDirectionComparison
import OAI.Analysis.RieszRectifiability.Restart.CoherentStoppingDichotomy

namespace OAI

/-!
# Comparing planes at adjacent cell scales

The factor of sixty-four between parent and child radii allows bilateral approximation
to transfer plane tubes across adjacent cells. A local plane comparison then bounds the
component of each child-plane direction orthogonal to the parent-plane direction.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem SupportCellDescendant.radius_parent_eq_64 {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i q : SupportCellDescendant μ R hR k z) (hdepth : i.depth = q.depth + 1) :
    q.radius = 64 * i.radius := by
  change latticeRadius R (k + q.depth) = 64 * latticeRadius R (k + i.depth)
  rw [hdepth, ← Nat.add_assoc, latticeRadius_succ]
  ring

theorem adjacent_cell_plane_tube_transfer {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (i q : SupportCellDescendant μ R hR k z) (hdepth : i.depth = q.depth + 1)
    (hcenter : i.center ∈ q.cell)
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (hSi : bilateralPlaneError μ i.center (1024 * i.radius) S < 1 / 1024)
    (hWq : bilateralPlaneError μ q.center (1024 * q.radius) W < 1 / 1024) :
    ∀ x ∈ ball i.center (1024 * i.radius), x ∈ S →
      infDist x (W : Set (Ambient d)) ≤ 65 * i.radius := by
  have hμ : μ.support.Nonempty := ⟨i.center, i.center_mem_support⟩
  obtain ⟨_, hreverse⟩ := bilateralPlaneError_lt_pointwise μ hμ i.center (1024 * i.radius)
    (1 / 1024) (mul_pos (by norm_num) i.radius_pos) S hS hSi
  obtain ⟨hforward, _⟩ := bilateralPlaneError_lt_pointwise μ hμ q.center (1024 * q.radius)
    (1 / 1024) (mul_pos (by norm_num) q.radius_pos) W hW hWq
  have hscale := i.radius_parent_eq_64 q hdepth
  have hcenters := q.dist_center_of_mem i.center hcenter
  intro x hx hxS
  have hxμ : infDist x μ.support < i.radius := by
    have h := hreverse x hx hxS
    linarith
  obtain ⟨y, hyμ, hxy⟩ := (infDist_lt_iff hμ).mp hxμ
  have hyball : y ∈ ball q.center (1024 * q.radius) := by
    have htri := dist_triangle y x q.center
    have htri' := dist_triangle x i.center q.center
    have hxb : dist x i.center < 1024 * i.radius := hx
    rw [dist_comm y x] at htri
    rw [mem_ball]
    have hr := i.radius_pos
    linarith
  have hyW : infDist y (W : Set (Ambient d)) < q.radius := by
    have h := hforward y hyball hyμ
    linarith
  calc
    _ ≤ infDist y (W : Set (Ambient d)) + dist x y := infDist_le_infDist_add_dist
    _ ≤ 65 * i.radius := by linarith

theorem adjacent_cell_plane_direction_bound {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (i q : SupportCellDescendant μ R hR k z) (hdepth : i.depth = q.depth + 1)
    (hcenter : i.center ∈ q.cell)
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (hSi : bilateralPlaneError μ i.center (1024 * i.radius) S < 1 / 1024)
    (hWq : bilateralPlaneError μ q.center (1024 * q.radius) W < 1 / 1024) :
    ∀ v ∈ S.direction,
      ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (65 / 384 : ℝ) * ‖v‖ := by
  let : Nonempty S := hS.1.to_subtype
  let : Nonempty W := hW.1.to_subtype
  let a : Ambient d := orthogonalProjection S i.center
  have haS : a ∈ S := orthogonalProjection_mem i.center
  obtain ⟨hforward, _⟩ := bilateralPlaneError_lt_pointwise μ
    ⟨i.center, i.center_mem_support⟩ i.center (1024 * i.radius) (1 / 1024)
    (mul_pos (by norm_num) i.radius_pos) S hS hSi
  have ha : dist a i.center ≤ i.radius := by
    have h := hforward i.center (mem_ball_self (mul_pos (by norm_num) i.radius_pos)) i.center_mem_support
    have heq : dist a i.center = infDist i.center (S : Set (Ambient d)) := by
      rw [dist_comm]
      exact dist_orthogonalProjection_eq_infDist S i.center
    rw [heq]
    linarith
  have htube : ∀ x ∈ S, x ∈ closedBall a (768 * i.radius) →
      infDist x (W : Set (Ambient d)) ≤ (65 / 768 : ℝ) * (768 * i.radius) := by
    intro x hxS hxball
    have hxlarge : x ∈ ball i.center (1024 * i.radius) := by
      have htri := dist_triangle x a i.center
      have hx : dist x a ≤ 768 * i.radius := hxball
      rw [mem_ball]
      have hr := i.radius_pos
      linarith
    have h := adjacent_cell_plane_tube_transfer μ R hR k z i q hdepth hcenter S W hS hW hSi hWq x hxlarge hxS
    linarith
  have h := direction_normal_bound_of_local_plane_tube S W a haS (768 * i.radius)
    (65 / 768) (mul_pos (by norm_num) i.radius_pos) htube
  intro v hv
  convert! h v hv using 1
  ring

end

end RieszRectifiability

end OAI
