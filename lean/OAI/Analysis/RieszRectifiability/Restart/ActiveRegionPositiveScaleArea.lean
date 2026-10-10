import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlaneDiskHausdorffMeasure
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleCharts
import OAI.Analysis.RieszRectifiability.Foundations.VitaliLocalMassCharge

namespace OAI

/-!
Positive stopping-scale charts bound the local Hausdorff area of an active-region limit
surface by a finite dimensional constant times the cell radius to the power `n`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionLocalAreaConstant (n d : ℕ) : ℝ≥0∞ :=
  (((activeProjectionGlobalLipschitzConstant d) ^ 3 * 2 : ℝ≥0) : ℝ≥0∞) ^ n *
    (ENNReal.ofReal (5 / 2)) ^ n * planeUnitHausdorffMeasure n

theorem activeRegionLocalAreaConstant_lt_top (n d : ℕ) :
    activeRegionLocalAreaConstant n d < ⊤ := by
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (planeUnitHausdorffMeasure_lt_top n)

theorem active_region_positive_scale_area_le {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (A : Set (Ambient d))
    (hnear : A ⊆ closedBall q.center ((17 / 8 : ℝ) * q.radius))
    (hscale : ∀ x ∈ A, q.radius / 8192 ≤ cellRegionStoppingScale μ R hR k z Good x) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ A) ≤
      activeRegionLocalAreaConstant n d * (ENNReal.ofReal q.radius) ^ n := by
  obtain ⟨g, hgLip, hgCover⟩ := exists_active_region_positive_scale_chart μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel q hq A hnear hscale
  have harea := plane_disk_lipschitz_range_hausdorffMeasure_le (S q).direction (hS q).2
    ((S q).direction.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius)
    (by have hr := q.radius_pos; positivity) _ g hgLip
  apply (measure_mono hgCover).trans
  convert! harea using 1
  unfold activeRegionLocalAreaConstant
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5 / 2), mul_pow]
  ring

end

end RieszRectifiability

end OAI
