import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceSuccessorMovement
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceInnerCone

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)

theorem active_successor_parent_captures_five_ball
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1)) :
    ∃ q ∈ activeLevelIndex μ R hR k z Good t,
      q.radius = 64 * i.radius ∧ dist i.center q.center ≤ 2 * q.radius ∧
      closedBall i.center (5 * i.radius) ⊆
        closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  obtain ⟨q, hqdepth, hsub, hc⟩ := i.exists_ancestor_at_depth t (by rw [hiA.1]; omega)
  have hqA : activeRegionCell Good q :=
    activeRegionCell_ancestor Good i q hiA.2 (by rw [hqdepth, hiA.1]; omega) hsub
  have hq : q ∈ activeLevelIndex μ R hR k z Good t :=
    (mem_activeLevelIndex μ R hR k z Good t q).mpr ⟨hqdepth, hqA⟩
  have hscale : q.radius = 64 * i.radius := by
    simp only [SupportCellDescendant.radius, hqdepth, hiA.1]
    rw [← Nat.add_assoc, latticeRadius_succ]
    ring
  have hcenters := q.dist_center_of_mem i.center hc
  refine ⟨q, hq, hscale, hcenters, ?_⟩
  intro x hx
  change dist x i.center ≤ 5 * i.radius at hx
  change dist x q.center ≤ (9 / 4 : ℝ) * q.radius
  have ht := dist_triangle x i.center q.center
  have hr := i.radius_pos
  nlinarith

variable (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεsmall : ε ≤ 1 / 1024)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (A : Set (Ambient d)) (hcharts : HasActiveSurfaceCharts μ R hR k z Good t S ε A)

include hS hε hεsmall hfit hcharts

theorem active_successor_plane_height_on_five_ball
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1))
    (x : Ambient d) (hx : x ∈ A) (hnear : x ∈ closedBall i.center (5 * i.radius)) :
    infDist x (S i : Set (Ambient d)) ≤ (17039360 * ε) * i.radius := by
  obtain ⟨q, hq, hscale, hcenters, hballs⟩ :=
    active_successor_parent_captures_five_ball μ R hR k z Good t i hi
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hp := (hcharts q hq).height_on_inner_ball q (S q) ε A x hx (hballs hnear)
  have hπ := neighbor_cell_affine_projections_close_on_32ball μ R hR k z i q
    (by rw [hscale]; have hr := i.radius_pos; linarith) (by rw [hscale])
    (by have hr := q.radius_pos; linarith)
    ε hε hεsmall (S i) (S q) (hS i) (hS q) (hfit i hiA.2) (hfit q hqA.2) x
    (by change dist x i.center ≤ 32 * i.radius; have hr := i.radius_pos; exact le_trans hnear (by linarith))
  have ht := dist_triangle (nonemptyAffineProjection (S i) (hS i).1 x)
    (nonemptyAffineProjection (S q) (hS q).1 x) x
  rw [nonemptyAffineProjection_dist_self, nonemptyAffineProjection_dist_self] at ht
  rw [hscale] at hp
  nlinarith

theorem active_successor_projection_residual_on_five_ball
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1))
    (x y : Ambient d) (hx : x ∈ A) (hy : y ∈ A)
    (hxnear : x ∈ closedBall i.center (5 * i.radius))
    (hynear : y ∈ closedBall i.center (5 * i.radius)) :
    ‖(nonemptyAffineProjection (S i) (hS i).1 x - x) -
      (nonemptyAffineProjection (S i) (hS i).1 y - y)‖ ≤
        (4 * activeProjectionError d ε + 2048 * ε) * dist x y := by
  obtain ⟨q, hq, hscale, hcenters, hballs⟩ :=
    active_successor_parent_captures_five_ball μ R hR k z Good t i hi
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hn := (hcharts q hq).normal_increment_on_inner_ball q (S q) ε hε.le A
    x y hx hy (hballs hxnear) (hballs hynear)
  have hop := neighbor_cell_projection_operator_norm_le μ R hR k z i q
    (by rw [hscale]; have hr := i.radius_pos; linarith) (by rw [hscale])
    (by have hr := q.radius_pos; linarith)
    ε hε hεsmall (S i) (S q) (hS i) (hS q) (hfit i hiA.2) (hfit q hqA.2)
  have hd := nonemptyAffineProjection_increment_difference_le (S i) (S q)
    (hS i).1 (hS q).1 x y (2048 * ε) hop
  have hparent : ‖(nonemptyAffineProjection (S q) (hS q).1 x -
      nonemptyAffineProjection (S q) (hS q).1 y) - (x - y)‖ ≤
      (4 * activeProjectionError d ε) * dist x y := by
    rw [nonemptyAffineProjection_sub]
    rw [(S q).direction.starProjection_orthogonal_val, norm_sub_rev] at hn
    exact hn
  have hid : (nonemptyAffineProjection (S i) (hS i).1 x - x) -
      (nonemptyAffineProjection (S i) (hS i).1 y - y) =
      ((nonemptyAffineProjection (S i) (hS i).1 x -
        nonemptyAffineProjection (S i) (hS i).1 y) -
       (nonemptyAffineProjection (S q) (hS q).1 x -
        nonemptyAffineProjection (S q) (hS q).1 y)) +
      ((nonemptyAffineProjection (S q) (hS q).1 x -
        nonemptyAffineProjection (S q) (hS q).1 y) - (x - y)) := by abel
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add hd hparent).trans_eq (by ring))

end

end RieszRectifiability

end OAI
