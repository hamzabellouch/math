import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveScaleBallSelection

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
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hε hεtiny hsmall hfit hmodel

theorem active_region_stopping_ball_area_le (x : Ambient d)
    (hpos : 0 < cellRegionStoppingScale μ R hR k z Good x)
    (hDs : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + 1)) :
    (μH[(n : ℝ)] : Measure (Ambient d))
      (Set.range f ∩ closedBall x (cellRegionStoppingScale μ R hR k z Good x / 16)) ≤
      (activeRegionLocalAreaConstant n d * (4096 : ℝ≥0∞) ^ n) *
        (ENNReal.ofReal (cellRegionStoppingScale μ R hR k z Good x)) ^ n := by
  obtain ⟨q, hq, hrhi, hrlo, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good x hpos hDs
  obtain ⟨hball, hscale⟩ := active_stopping_ball_chart_geometry μ R hR k z Good x q hrhi hrlo hnear
  have harea := active_region_positive_scale_area_le μ R hR k z Good S hS ε hε hεtiny hsmall
    hfit f hmodel q hq _ hball hscale
  apply harea.trans
  have hrad : ENNReal.ofReal q.radius ≤
      (4096 : ℝ≥0∞) * ENNReal.ofReal (cellRegionStoppingScale μ R hR k z Good x) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4096), ENNReal.ofReal_ofNat]
      using! ENNReal.ofReal_le_ofReal hrhi
  calc
    _ ≤ activeRegionLocalAreaConstant n d *
        ((4096 : ℝ≥0∞) * ENNReal.ofReal (cellRegionStoppingScale μ R hR k z Good x)) ^ n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

theorem active_region_limit_support_distance_at_scale (x : Ambient d)
    (hx : x ∈ Set.range f)
    (hpos : 0 < cellRegionStoppingScale μ R hR k z Good x)
    (hDs : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + 1)) :
    infDist x μ.support ≤ (2187264000 * ε) * cellRegionStoppingScale μ R hR k z Good x := by
  obtain ⟨q, hq, hrhi, _, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good x hpos hDs
  obtain ⟨u, rfl⟩ := hx
  let y := activeRegionParameterMap μ R hR k z Good S hS q.depth u
  have hy : y ∈ activeRegionSurface μ R hR k z Good S hS q.depth := by
    rw [activeRegionSurface_eq_image]
    exact ⟨u, u.property, rfl⟩
  have hmove : dist y (f u) ≤ ((17039360 * ε) / 63) * q.radius :=
    hmodel.2.2.2.1 q.depth u
  have hr := q.radius_pos
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr.le
  have hylocal : y ∈ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + q.depth)) := by
    have htri := dist_triangle y (f u) q.center
    change dist y q.center ≤ (9 / 4 : ℝ) * q.radius
    nlinarith
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  have hyμ := activeRegionSurface_near_support_in_active_ball μ R hR k z Good S hS ε hε
    hεtiny hsmall hfit q.depth q hqF y hy hylocal
  change infDist y μ.support ≤ (263168 * ε) * q.radius at hyμ
  have hinf : infDist (f u) μ.support ≤ infDist y μ.support + dist (f u) y :=
    infDist_le_infDist_add_dist
  rw [dist_comm (f u) y] at hinf
  have hlocal : infDist (f u) μ.support ≤ (534000 * ε) * q.radius := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hrhi (show 0 ≤ 534000 * ε by positivity)
  nlinarith

end

end RieszRectifiability

end OAI
