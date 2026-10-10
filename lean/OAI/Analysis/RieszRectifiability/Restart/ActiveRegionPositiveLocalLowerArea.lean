import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleInnerDisk
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionHighScaleInnerDisk
import OAI.Analysis.RieszRectifiability.Surfaces.PlaneDiskLowerArea

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionPositiveLocalLowerAreaConstant (n : ℕ) : ℝ≥0∞ :=
  planeDiskLowerAreaConstant n 64 * (ENNReal.ofReal (1 / 16 : ℝ)) ^ n

theorem activeRegionPositiveLocalLowerAreaConstant_pos (n : ℕ) :
    0 < activeRegionPositiveLocalLowerAreaConstant n := by
  exact ENNReal.mul_pos (planeDiskLowerAreaConstant_pos n 64).ne' (by positivity)

theorem activeRegionPositiveLocalLowerAreaConstant_lt_top (n : ℕ) :
    activeRegionPositiveLocalLowerAreaConstant n < ⊤ := by
  exact ENNReal.mul_lt_top (planeDiskLowerAreaConstant_lt_top n 64 (by norm_num))
    (by finiteness)

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

theorem active_region_positive_scale_local_ball_area_ge
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p)
    (hDsmall : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1))
    (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ cellRegionStoppingScale μ R hR k z Good p / 2) :
    activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  obtain ⟨q, _, a, H, _, hsep, _, hinto⟩ :=
    exists_active_region_positive_scale_inner_disk μ R hR k z Good S hS ε hε hεtiny
      hsmall hfit f hmodel p hp hDpos hDsmall r hr hrsmall
  have h := (plane_disk_antilipschitz_range_hausdorffMeasure_ge (S q).direction
    (hS q).2 a (r / 16) (by positivity) 64 (by norm_num) H hsep).trans (measure_mono hinto)
  have heq : planeDiskLowerAreaConstant n 64 * (ENNReal.ofReal (r / 16)) ^ n =
      activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal r) ^ n := by
    rw [show r / 16 = (1 / 16) * r by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 16), mul_pow]
    exact (mul_assoc _ _ _).symm
  rwa [heq] at h

theorem active_region_high_scale_local_ball_area_ge
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hD : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p)
    (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ latticeRadius R k / 128) :
    activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  obtain ⟨a, H, _, hsep, _, hinto⟩ :=
    exists_active_region_high_scale_inner_disk μ R hR k z Good S hS ε hε hεtiny
      hsmall hfit f hmodel p hp hD r hr hrsmall
  have h := (plane_disk_antilipschitz_range_hausdorffMeasure_ge
    (S (supportCellRoot μ R hR k z)).direction (hS _).2 a (r / 4)
    (by positivity) 16 (by norm_num) H hsep).trans (measure_mono hinto)
  have hcoeff : planeDiskLowerAreaConstant n 64 ≤ planeDiskLowerAreaConstant n 16 := by
    unfold planeDiskLowerAreaConstant
    gcongr
    norm_num
  have hrad : ENNReal.ofReal (r / 16) ≤ ENNReal.ofReal (r / 4) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have heq : activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal r) ^ n =
      planeDiskLowerAreaConstant n 64 * (ENNReal.ofReal (r / 16)) ^ n := by
    rw [show r / 16 = (1 / 16) * r by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 16), mul_pow]
    exact mul_assoc _ _ _
  rw [heq]
  exact (mul_le_mul' hcoeff (pow_le_pow_left' hrad n)).trans h

theorem active_region_positive_stopping_scale_local_ball_area_ge
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p)
    (r : ℝ) (hr : 0 < r)
    (hrscale : r ≤ cellRegionStoppingScale μ R hR k z Good p / 2)
    (hrtop : r ≤ latticeRadius R k / 128) :
    activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  by_cases hD : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1)
  · exact active_region_positive_scale_local_ball_area_ge μ R hR k z Good S hS ε
      hε hεtiny hsmall hfit f hmodel p hp hDpos hD r hr hrscale
  · exact active_region_high_scale_local_ball_area_ge μ R hR k z Good S hS ε
      hε hεtiny hsmall hfit f hmodel p hp (le_of_not_gt hD) r hr hrtop

end

end RieszRectifiability

end OAI
