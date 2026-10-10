import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLargeScaleCharts
import OAI.Analysis.RieszRectifiability.Flatness.PlaneDiskHausdorffMeasure

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionLargeAreaConstant (n d : ℕ) : ℝ≥0∞ :=
  (((activeProjectionGlobalLipschitzConstant d) ^ 2 : ℝ≥0) : ℝ≥0∞) ^ n *
    (3 : ℝ≥0∞) ^ n * planeUnitHausdorffMeasure n

theorem activeRegionLargeAreaConstant_lt_top (n d : ℕ) :
    activeRegionLargeAreaConstant n d < ⊤ := by
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) (by finiteness))
    (planeUnitHausdorffMeasure_lt_top n)

theorem active_region_large_scale_area_le {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 ≤ ε)
    (hεtiny : ε ≤ 1 / 268435456)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (A : Set (Ambient d)) (hA : A ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k))
    (hD : ∀ x ∈ A, latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ A) ≤
      activeRegionLargeAreaConstant n d * (ENNReal.ofReal (latticeRadius R k)) ^ n := by
  obtain ⟨g, hgLip, hgCover⟩ := exists_active_region_large_scale_chart μ R hR k z Good S hS ε hε
    hεtiny hfit f hmodel A hA hD
  have harea := plane_disk_lipschitz_range_hausdorffMeasure_le
    (S (supportCellRoot μ R hR k z)).direction (hS _).2 _ (3 * latticeRadius R k)
    (by have hr := latticeRadius_pos R hR k; positivity) _ g hgLip
  apply (measure_mono hgCover).trans
  convert! harea using 1
  unfold activeRegionLargeAreaConstant
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat, mul_pow]
  ring

end

end RieszRectifiability

end OAI
