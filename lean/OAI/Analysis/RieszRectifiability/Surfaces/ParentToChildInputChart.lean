import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.RecenteredDiskCharts
import OAI.Analysis.RieszRectifiability.Projections.ProjectionTubeLocation
import OAI.Analysis.RieszRectifiability.Surfaces.ParentChartPlaneHeight
import OAI.Analysis.RieszRectifiability.Surfaces.PlaneChangeCharts

namespace OAI

/-!
# Parent-to-child input charts

A parent chart is reparametrized over the nearby child plane and restricted to the child
disk. Projection and height estimates preserve the exact restricted range, the Lipschitz
and normal-component bounds, and containment in the physical child ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_parent_to_child_input_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (i q : SupportCellDescendant μ R hR k z)
    (hscale : q.radius = 64 * i.radius)
    (hnear : dist i.center q.center ≤ 2 * q.radius)
    (ε : ℝ) (hε : 0 < ε) (hεtiny : ε ≤ 1 / 268435456)
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (hSi : bilateralPlaneError μ i.center (1024 * i.radius) S < ε)
    (hWq : bilateralPlaneError μ q.center (1024 * q.radius) W < ε)
    (g : closedBall (W.direction.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) → Ambient d)
    (L : ℝ≥0) (hsmall : (L : ℝ) + 2048 * ε ≤ 1 / 8)
    (hcoordinates : ∀ u, W.direction.orthogonalProjectionOnto (g u) = u.val)
    (hnormal : LipschitzWith L
      (fun u => (W.directionᗮ : Submodule ℝ (Ambient d)).starProjection (g u)))
    (hheight : ∀ u, infDist (g u) (W : Set (Ambient d)) ≤ (262144 * ε) * q.radius)
    (hphysical : ∀ u, g u ∈ closedBall q.center (3 * q.radius)) :
    ∃ h : closedBall (S.direction.orthogonalProjectionOnto i.center) ((11 / 4 : ℝ) * i.radius) → Ambient d,
      LipschitzWith 2 h ∧
      LipschitzWith (2 * (L + Real.toNNReal (2048 * ε)))
        (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ Set.range g ∧ S.direction.orthogonalProjectionOnto (h u) = u.val ∧
        h u ∈ closedBall i.center (3 * i.radius)) ∧
      Set.range h = Set.range g ∩ S.direction.orthogonalProjectionOnto ⁻¹'
        closedBall (S.direction.orthogonalProjectionOnto i.center) ((11 / 4 : ℝ) * i.radius) := by
  let P := W.direction
  let Q := S.direction
  let a := P.orthogonalProjectionOnto q.center
  let ac := Q.orthogonalProjectionOnto i.center
  let ρ := (5 / 2 : ℝ) * q.radius
  have hri := i.radius_pos
  have hrq := q.radius_pos
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let u0 : closedBall a ρ := ⟨a, mem_closedBall_self hρ.le⟩
  let b := Q.orthogonalProjectionOnto (g u0)
  let α : ℝ≥0 := ⟨2048 * ε, by positivity⟩
  have hα : α = Real.toNNReal (2048 * ε) := by
    apply Subtype.ext
    exact (Real.coe_toNNReal _ (by positivity : 0 ≤ 2048 * ε)).symm
  have hεsmall : ε ≤ 1 / 1024 := by linarith
  have hop := neighbor_cell_projection_operator_norm_le μ R hR k z i q
    (by rw [hscale]; linarith) hscale.le (by linarith)
    ε hε hεsmall S W hS hW hSi hWq
  have hop' : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ) := by
    rw [norm_sub_rev]
    exact hop
  have hsmall' : (L : ℝ) + (α : ℝ) ≤ 1 / 4 := by
    change (L : ℝ) + 2048 * ε ≤ 1 / 4
    linarith
  have hcq := (bilateralPlaneError_lt_pointwise μ ⟨q.center, q.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) W hW hWq).1 q.center
      (mem_ball_self (by positivity)) q.center_mem_support
  have hci := (bilateralPlaneError_lt_pointwise μ ⟨i.center, i.center_mem_support⟩
    i.center (1024 * i.radius) ε (by positivity) S hS hSi).1 i.center
      (mem_ball_self (by positivity)) i.center_mem_support
  have hx0 : dist (g u0) q.center ≤ (263168 * ε) * q.radius := by
    have h := dist_le_projection_add_plane_distances W hW.1 (g u0) q.center
    have hc : P.starProjection (g u0) = P.starProjection q.center :=
      congrArg (fun v : P => (v : Ambient d)) (hcoordinates u0)
    change dist (g u0) q.center ≤ dist (P.starProjection (g u0)) (P.starProjection q.center) +
      infDist (g u0) (W : Set (Ambient d)) + infDist q.center (W : Set (Ambient d)) at h
    rw [hc, dist_self, zero_add] at h
    nlinarith [hheight u0]
  have hx0small : dist (g u0) q.center ≤ q.radius / 16 := by
    have hm := mul_le_mul_of_nonneg_right hεtiny hrq.le
    nlinarith
  have hb : dist ac b ≤ 2 * q.radius + q.radius / 16 := by
    have hp := Q.norm_starProjection_apply_le (i.center - g u0)
    rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
    have ht := dist_triangle i.center q.center (g u0)
    rw [dist_comm q.center (g u0)] at ht
    change dist (Q.starProjection i.center) (Q.starProjection (g u0)) ≤ _
    linarith
  obtain ⟨hradius, j, hjLip, hjNormal, hjCoords, hjRange⟩ :=
    exists_chart_over_nearby_plane P Q a ρ hρ g L α hsmall' hcoordinates hnormal hop'
  have hcontain : dist ac b + (11 / 4 : ℝ) * i.radius ≤
      ρ - ((L : ℝ) + (α : ℝ)) * ρ := by
    have hm := mul_le_mul_of_nonneg_right hsmall hrq.le
    change dist ac b + (11 / 4 : ℝ) * i.radius ≤
      (5 / 2 : ℝ) * q.radius - ((L : ℝ) + 2048 * ε) * ((5 / 2 : ℝ) * q.radius)
    nlinarith
  obtain ⟨h, hhLip, hhNormal, hhCoords, hhRange⟩ :=
    exists_recentered_disk_chart Q b (ρ - ((L : ℝ) + (α : ℝ)) * ρ) j (2 * (L + α))
      (fun u => (hjCoords u).2) hjNormal ac ((11 / 4 : ℝ) * i.radius) hcontain
  have hL : 1 + 2 * (L + α) ≤ (2 : ℝ≥0) := by
    have hreal : ((1 + 2 * (L + α) : ℝ≥0) : ℝ) ≤ 2 := by
      change 1 + 2 * ((L : ℝ) + 2048 * ε) ≤ 2
      linarith
    exact_mod_cast hreal
  have hrange : Set.range h = Set.range g ∩ Q.orthogonalProjectionOnto ⁻¹'
      closedBall ac ((11 / 4 : ℝ) * i.radius) := by
    rw [hhRange, hjRange]
    ext y
    constructor
    · intro hy
      exact ⟨hy.1.1, hy.2⟩
    · intro hy
      refine ⟨⟨hy.1, ?_⟩, hy.2⟩
      have hy' : dist (Q.orthogonalProjectionOnto y) ac ≤ (11 / 4 : ℝ) * i.radius := hy.2
      have ht := dist_triangle (Q.orthogonalProjectionOnto y) ac b
      change dist (Q.orthogonalProjectionOnto y) b ≤ ρ - ((L : ℝ) + (α : ℝ)) * ρ
      linarith
  have hhg : ∀ u, h u ∈ Set.range g := by
    intro u
    exact (hrange ▸ (show h u ∈ Set.range h from ⟨u, rfl⟩)).1
  have hhheight : ∀ u, infDist (h u) (S : Set (Ambient d)) ≤ (524288 * ε) * q.radius := by
    intro u
    obtain ⟨v, hv⟩ := hhg u
    rw [← hv]
    exact parent_chart_plane_height_transfer μ R hR k z i q hscale hnear ε hε hεsmall
      S W hS hW hSi hWq (g v) (hphysical v) (hheight v)
  have hhphysical : ∀ u, h u ∈ closedBall i.center (3 * i.radius) := by
    intro u
    have hloc := plane_chart_location_of_height S hS.1 i.center ((11 / 4 : ℝ) * i.radius)
      ((524288 * ε) * q.radius) h (fun v => (hhCoords v).2) hhheight u
    have hm := mul_le_mul_of_nonneg_right hεtiny hri.le
    rw [hscale] at hloc
    change dist (h u) i.center ≤ 3 * i.radius
    nlinarith
  refine ⟨h, hhLip.weaken hL, ?_, ?_, hrange⟩
  · rwa [← hα]
  · intro u
    exact ⟨hhg u, (hhCoords u).2, hhphysical u⟩

end

end RieszRectifiability

end OAI
