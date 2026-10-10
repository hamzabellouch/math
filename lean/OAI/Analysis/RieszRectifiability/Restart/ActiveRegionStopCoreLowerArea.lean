import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveLocalLowerArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionStopCoreStabilization

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hε hεfine hsmall hfit hmodel

theorem exists_active_region_limit_point_near_stop_center
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hdepth : 0 < i.depth) :
    ∃ x ∈ Set.range f, dist x i.center ≤ i.radius / 1024 := by
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  obtain ⟨q, hqdepth, hsub, hc⟩ := i.exists_ancestor_at_depth (i.depth - 1) (Nat.sub_le _ _)
  have hid : i.depth = q.depth + 1 := by omega
  have hqA := activeRegionCell_of_strict_stop_ancestor Good i q hi (by omega) hsub
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hqA⟩
  have hscale : q.radius = 64 * i.radius := by
    change latticeRadius R (k + q.depth) = 64 * latticeRadius R (k + i.depth)
    rw [hid, ← Nat.add_assoc, latticeRadius_succ]
    ring
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth
  obtain ⟨y, hy, hnear⟩ := active_cell_support_point_near_surface μ R hR k z q (S q) (hS q)
    ε (hfit q hqA) (activeRegionSurface μ R hR k z Good S hS q.depth) (hcharts q hqF)
    i.center i.center_mem_support (q.dist_center_of_mem i.center hc)
  let x := activeRegionTransitionMap μ R hR k z Good S hS q.depth 3 y
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS
    ε hε.le f hmodel q.depth 3 y hy
  change dist x y ≤ (2 * ((17039360 * ε) / 63)) * q.radius at hmove
  have hclose : dist x i.center ≤ i.radius / 1024 := by
    have ht := dist_triangle x y i.center
    rw [dist_comm y i.center] at ht
    have hcoeff : (263168 * ε + 2 * ((17039360 * ε) / 63)) * 64 ≤ 1 / 1024 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff i.radius_pos.le
    rw [hscale] at hnear hmove
    nlinarith
  have hcore : x ∈ closedBall i.center (i.radius / 16) := by
    change dist x i.center ≤ i.radius / 16
    have hri := i.radius_pos
    linarith
  have hfinite : x ∈ activeRegionSurface μ R hR k z Good S hS (i.depth + 2) := by
    rw [show i.depth + 2 = q.depth + 3 by omega, activeRegionSurface_add]
    exact ⟨y, hy, rfl⟩
  have hstable := active_region_stop_core_stabilizes_after_two_levels μ R hR k z Good S hS
    ε hε.le hεtiny f hmodel i hi (i.depth + 2) le_rfl
  exact ⟨x, (hstable.symm ▸ (show x ∈ activeRegionSurface μ R hR k z Good S hS
    (i.depth + 2) ∩ closedBall i.center (i.radius / 16) from ⟨hfinite, hcore⟩)).1, hclose⟩

theorem active_region_stop_core_area_ge
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hdepth : 0 < i.depth) :
    activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (i.radius / 128)) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d))
        (Set.range f ∩ closedBall i.center (i.radius / 32)) := by
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  obtain ⟨x, hx, hclose⟩ := exists_active_region_limit_point_near_stop_center μ R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel i hi hdepth
  have hri := i.radius_pos
  have hcore : x ∈ closedBall i.center (i.radius / 16) := by
    change dist x i.center ≤ i.radius / 16
    linarith
  have hD := (cellRegionStoppingScale_stop_core_bounds μ R hR k z Good i hi x hcore).1
  have hri0 : i.radius ≤ latticeRadius R k := by
    exact latticeRadius_antitone R hR.le (Nat.le_add_right k i.depth)
  have harea := active_region_positive_stopping_scale_local_ball_area_ge μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel x hx (by linarith) (i.radius / 128) (by positivity)
    (by linarith) (by linarith)
  refine harea.trans (measure_mono ?_)
  intro y hy
  refine ⟨hy.1, ?_⟩
  have hyb : dist y x ≤ i.radius / 128 := hy.2
  have ht := dist_triangle y x i.center
  change dist y i.center ≤ i.radius / 32
  linarith

end

end RieszRectifiability

end OAI
