import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.LatticeRadiusAbove
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellMassArea

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def activeRegionLowScaleAreaFactor (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  (384 : ℝ≥0∞) ^ n * ENNReal.ofReal (C * 8 ^ n) *
    (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G)

theorem activeRegionLowScaleAreaFactor_pos (n : ℕ) (C G : ℝ) (hC : 0 < C) (hG : 0 < G) :
    0 < activeRegionLowScaleAreaFactor n C G := by
  have hfirst : 0 < (384 : ℝ≥0∞) ^ n * ENNReal.ofReal (C * 8 ^ n) := by
    exact ENNReal.mul_pos (by positivity) (by positivity)
  exact ENNReal.mul_pos hfirst.ne' (ne_of_gt (lt_of_lt_of_le
    (ENNReal.ofReal_pos.mpr hG) (le_add_right le_rfl)))

theorem activeRegionLowScaleAreaFactor_lt_top (n : ℕ) (C G : ℝ) :
    activeRegionLowScaleAreaFactor n C G < ⊤ := by
  have hs := activeRegionStopMassAreaConstant_lt_top n G
  unfold activeRegionLowScaleAreaFactor
  finiteness

def activeRegionSmallRadiusLowerAreaConstant (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  min (activeRegionLowScaleAreaFactor n C G)⁻¹
    (activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (1 / 1024 : ℝ)) ^ n)

theorem activeRegionSmallRadiusLowerAreaConstant_pos (n : ℕ) (C G : ℝ) :
    0 < activeRegionSmallRadiusLowerAreaConstant n C G := by
  apply lt_min
  · exact ENNReal.inv_pos.mpr (activeRegionLowScaleAreaFactor_lt_top n C G).ne
  · exact ENNReal.mul_pos (activeRegionPositiveLocalLowerAreaConstant_pos n).ne' (by positivity)

theorem activeRegionSmallRadiusLowerAreaConstant_lt_top (n : ℕ) (C G : ℝ) :
    activeRegionSmallRadiusLowerAreaConstant n C G < ⊤ := by
  exact lt_of_le_of_lt (min_le_right _ _) (ENNReal.mul_lt_top
    (activeRegionPositiveLocalLowerAreaConstant_lt_top n) (by finiteness))

variable {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
  (hg : GlobalUpperGrowth n G μ)
  (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
  (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hC hG hg hlower hcore hε hεfine hsmall hfit hmodel

theorem active_region_low_stopping_scale_ball_area_ge
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (hrtop : r ≤ 384 * latticeRadius R k)
    (hD : cellRegionStoppingScale μ R hR k z Good p < r / 384) :
    (activeRegionLowScaleAreaFactor n C G)⁻¹ * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  obtain ⟨t, htlo, hthi⟩ := exists_lattice_radius_above R k (r / 384) (by positivity) (by linarith)
  obtain ⟨q, hq, hpq⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good t p
    (hD.trans_le htlo)
  have hqr : q.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hq.1]
  rw [← hqr] at htlo hthi hpq
  have hsub : Set.range f ∩ closedBall q.center (3 * q.radius) ⊆
      Set.range f ∩ closedBall p r := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hxq : dist x q.center ≤ 3 * q.radius := hx.2
    have ht := dist_triangle x q.center p
    rw [dist_comm q.center p] at ht
    change dist x p ≤ r
    linarith
  have harea := active_cell_radius_power_le_limit_area μ G hG hg R hR k z Good S hS ε
    hε hεfine hsmall hfit f hmodel C hC hlower hcore q hq.2
  have hrq : (ENNReal.ofReal r) ^ n ≤ (384 : ℝ≥0∞) ^ n * (ENNReal.ofReal q.radius) ^ n := by
    have h : r ≤ 384 * q.radius := by linarith
    have he := pow_le_pow_left' (ENNReal.ofReal_le_ofReal h) n
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 384),
      ENNReal.ofReal_ofNat, mul_pow] using! he
  have hbound : (ENNReal.ofReal r) ^ n ≤ activeRegionLowScaleAreaFactor n C G *
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
    calc
      _ ≤ (384 : ℝ≥0∞) ^ n * (ENNReal.ofReal q.radius) ^ n := hrq
      _ ≤ (384 : ℝ≥0∞) ^ n *
          ((ENNReal.ofReal (C * 8 ^ n) * (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G)) *
            (μH[(n : ℝ)] : Measure (Ambient d))
              (Set.range f ∩ closedBall q.center (3 * q.radius))) := mul_le_mul_right harea _
      _ ≤ (384 : ℝ≥0∞) ^ n *
          ((ENNReal.ofReal (C * 8 ^ n) * (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G)) *
            (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r)) := by
        gcongr
      _ = _ := by unfold activeRegionLowScaleAreaFactor; ring
  exact (ENNReal.inv_mul_le_iff (activeRegionLowScaleAreaFactor_pos n C G hC hG).ne'
    (activeRegionLowScaleAreaFactor_lt_top n C G).ne).mpr hbound

theorem active_region_limit_small_radius_ball_area_ge
    (p : Ambient d) (hp : p ∈ Set.range f)
    (r : ℝ) (hr : 0 < r) (hrtop : r ≤ latticeRadius R k) :
    activeRegionSmallRadiusLowerAreaConstant n C G * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  by_cases hD : cellRegionStoppingScale μ R hR k z Good p < r / 384
  · have h := active_region_low_stopping_scale_ball_area_ge μ C G hC hG hg hlower R hR k hcore
      z Good S hS ε hε hεfine hsmall hfit f hmodel p r hr (by linarith) hD
    exact (mul_le_mul_left (min_le_left _ _) _).trans h
  · have hDlarge : r / 384 ≤ cellRegionStoppingScale μ R hR k z Good p := le_of_not_gt hD
    have harea := active_region_positive_stopping_scale_local_ball_area_ge μ R hR k z Good S hS
      ε hε (by linarith) hsmall hfit f hmodel p hp (by linarith) (r / 1024) (by positivity)
      (by linarith) (by linarith)
    have hsub : Set.range f ∩ closedBall p (r / 1024) ⊆ Set.range f ∩ closedBall p r := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      have hxp : dist x p ≤ r / 1024 := hx.2
      change dist x p ≤ r
      linarith
    have heq : activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (r / 1024)) ^ n =
        (activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (1 / 1024 : ℝ)) ^ n) *
          (ENNReal.ofReal r) ^ n := by
      rw [show r / 1024 = (1 / 1024) * r by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 1024), mul_pow]
      exact (mul_assoc _ _ _).symm
    rw [heq] at harea
    exact ((mul_le_mul_left (min_le_right _ _) _).trans harea).trans (measure_mono hsub)

end

end RieszRectifiability

end OAI
