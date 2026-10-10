import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitProjectionCoverage
import OAI.Analysis.RieszRectifiability.Flatness.ContractedDirectionTube

namespace OAI

/-!
# Local flatness of active-region limits

Finite-stage charts lift into the limiting parameterization with controlled
tangential displacement and normal error. These estimates bound the height of the
limit over each active fitting plane and, conversely, approximate nearby points
of that plane by points of the limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology EuclideanGeometry

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hε hεtiny hsmall hfit hmodel

theorem exists_active_region_limit_chart_with_normal_error
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q) :
    ∃ H : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        ((5 / 2 : ℝ) * q.radius) → Ambient d,
      Continuous H ∧ Set.range H ⊆ Set.range f ∧
      (∀ u, dist ((S q).direction.orthogonalProjectionOnto (H u)) u.val ≤
        ((17039360 * ε) / 63) * q.radius) ∧
      (∀ u, infDist (H u) (S q : Set (Ambient d)) ≤ (534000 * ε) * q.radius) ∧
      (∀ u, H u ∈ closedBall q.center (4 * q.radius)) := by
  have hqi : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  obtain ⟨g, hg, _, hcoords, _⟩ :=
    activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth q hqi
  obtain ⟨j, hj, hjF⟩ := exists_active_region_finite_chart_lift μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit q.depth g 2 hg
    (by rintro _ ⟨a, rfl⟩; exact (hcoords a).1)
  let H := fun a => f (j a)
  have hdisp (a) : dist (H a) (g a) ≤ ((17039360 * ε) / 63) * q.radius := by
    have ht := hmodel.2.2.2.1 q.depth (j a)
    rw [hjF a, dist_comm] at ht
    exact ht
  refine ⟨H, hmodel.1.comp hj.continuous, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨j a, rfl⟩
  · intro a
    rw [← (hcoords a).2.1]
    have hp := (S q).direction.norm_starProjection_apply_le (H a - g a)
    rw [map_sub] at hp
    exact hp.trans (hdisp a)
  · intro a
    have hi : infDist (H a) (S q : Set (Ambient d)) ≤
        infDist (g a) (S q : Set (Ambient d)) + dist (H a) (g a) :=
      infDist_le_infDist_add_dist
    have hgplane := (hcoords a).2.2.1
    nlinarith [hdisp a, q.radius_pos]
  · intro a
    have ht := dist_triangle (H a) (g a) q.center
    have hgball : dist (g a) q.center ≤ 3 * q.radius := (hcoords a).2.2.2
    have hB : (17039360 * ε) / 63 ≤ 1 / 2 := by nlinarith
    have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
    change dist (H a) q.center ≤ 4 * q.radius
    nlinarith [hdisp a, q.radius_pos]

theorem active_region_limit_height_on_active_ball
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (x : Ambient d) (hx : x ∈ Set.range f) (hlocal : x ∈ closedBall q.center (2 * q.radius)) :
    infDist x (S q : Set (Ambient d)) ≤ (534000 * ε) * q.radius := by
  obtain ⟨u, rfl⟩ := hx
  let y := activeRegionParameterMap μ R hR k z Good S hS q.depth u
  have hy : y ∈ activeRegionSurface μ R hR k z Good S hS q.depth := by
    rw [activeRegionSurface_eq_image]
    exact ⟨u, u.property, rfl⟩
  have htail : dist y (f u) ≤ ((17039360 * ε) / 63) * q.radius :=
    hmodel.2.2.2.1 q.depth u
  have hB : (17039360 * ε) / 63 ≤ 1 / 4 := by nlinarith
  have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
  have hylocal : y ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
    have ht := dist_triangle y (f u) q.center
    change dist (f u) q.center ≤ 2 * q.radius at hlocal
    change dist y q.center ≤ (9 / 4 : ℝ) * q.radius
    nlinarith
  have hqi : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  have hchart := activeRegionSurface_charts μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit q.depth q hqi
  have hyplane := hchart.height_on_inner_ball q (S q) ε _ y hy hylocal
  have hinf : infDist (f u) (S q : Set (Ambient d)) ≤
      infDist y (S q : Set (Ambient d)) + dist (f u) y := infDist_le_infDist_add_dist
  rw [dist_comm (f u) y] at hinf
  nlinarith [q.radius_pos]

theorem active_fitting_plane_approximated_by_limit
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (p : Ambient d) (hp : p ∈ S q) (hlocal : p ∈ closedBall q.center (2 * q.radius)) :
    ∃ x ∈ Set.range f ∩ closedBall q.center (4 * q.radius),
      dist p x ≤ (534000 * ε) * q.radius := by
  let : Nonempty (S q) := (hS q).1.to_subtype
  obtain ⟨H, hH, hrange, hdisp, hnormal, hball⟩ :=
    exists_active_region_limit_chart_with_normal_error μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel q hq
  let P := (S q).direction
  let a := P.orthogonalProjectionOnto p
  have ha : a ∈ closedBall (P.orthogonalProjectionOnto q.center)
      ((5 / 2 : ℝ) * q.radius - ((17039360 * ε) / 63) * q.radius) := by
    have hbound : dist a (P.orthogonalProjectionOnto q.center) ≤ dist p q.center := by
      change ‖P.starProjection p - P.starProjection q.center‖ ≤ ‖p - q.center‖
      rw [← map_sub]
      exact P.norm_starProjection_apply_le _
    have hB : (17039360 * ε) / 63 ≤ 1 / 2 := by nlinarith
    have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
    change dist p q.center ≤ 2 * q.radius at hlocal
    change dist a (P.orthogonalProjectionOnto q.center) ≤ _
    nlinarith
  obtain ⟨u, hu⟩ := closedBall_covered_by_continuous_perturbation
    (P.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius)
    (((17039360 * ε) / 63) * q.radius)
    (mul_nonneg (by norm_num) q.radius_pos.le)
    (fun u => P.orthogonalProjectionOnto (H u)) (P.orthogonalProjectionOnto.continuous.comp hH)
    hdisp ha
  have hP : P.starProjection (H u) = P.starProjection p :=
    congrArg (fun w : P => (w : Ambient d)) hu
  have heq : (orthogonalProjection (S q) (H u) : Ambient d) = p := by
    have hd := affine_projection_difference (S q) (H u) p
    rw [orthogonalProjection_eq_self_iff.mpr hp, map_sub, hP, sub_self] at hd
    exact sub_eq_zero.mp hd
  refine ⟨H u, ⟨hrange ⟨u, rfl⟩, hball u⟩, ?_⟩
  have hd := dist_orthogonalProjection_eq_infDist (S q) (H u)
  rw [heq, dist_comm] at hd
  rw [hd]
  exact hnormal u

end

end RieszRectifiability

end OAI
