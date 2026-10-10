import OAI.Analysis.CircleDomains.Modulus.FiniteCostChartPaths
import OAI.Analysis.CircleDomains.Sobolev.LipschitzMappedCost

namespace OAI

/-! Weighted cost of a chart interval, bounded by the ordinary line
integral of the pulled-back density. Parameter speed cancels exactly. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

def realRectifiableInterval (a b : ℝ) : RectifiablePath ℝ :=
  ⟨realIntervalPath a b, lipschitz_path_boundedVariation (realIntervalPath_lipschitz a b)⟩

theorem realRectifiableInterval_occupation_le {a b : ℝ} (hab : a < b) :
    pathOccupation (realRectifiableInterval a b) ≤ volume.restrict (Icc a b) := by
  have h := bilipschitz_pathOccupation_le (realRectifiableInterval a b)
    (realIntervalPath_lipschitz a b) (by simpa only [ne_eq, nndist_eq_zero] using hab.ne)
    (realIntervalPath_antilipschitz hab.ne)
  have hne : nndist a b ≠ 0 := by
    simpa only [ne_eq, nndist_eq_zero] using hab.ne
  have hc : (nndist a b : ℝ≥0∞) * ↑((nndist a b)⁻¹) = 1 := by
    rw [← ENNReal.coe_mul, mul_inv_cancel₀ hne, ENNReal.coe_one]
  rw [hc, one_smul] at h
  simpa only [realRectifiableInterval, range_realIntervalPath hab,
    hausdorffMeasure_real] using h

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem intervalChartPath_cost_le
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} (hab : a < b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y, g y ∂pathOccupation (intervalChartPath φ hab.le hL)) ≤
      (L : ℝ≥0∞) * ∫⁻t in Icc a b, g (φ t) := by
  let α := realRectifiableInterval a b
  have hα : ∀t, α.val t ∈ Icc a b := fun t => realIntervalPath_mem hab.le t
  have hcost := lipschitzMappedPath_cost_le α φ hL hα g hg
  change (∫⁻y, g y ∂pathOccupation (intervalChartPath φ hab.le hL)) ≤ _ at hcost
  apply hcost.trans
  apply mul_le_mul' le_rfl
  calc
    _ = ∫⁻t, g (φ t) ∂pathOccupation α := (lintegral_pathOccupation α (hg.comp hφ)).symm
    _ ≤ _ := lintegral_mono' (realRectifiableInterval_occupation_le hab) fun _ => le_rfl

end CircleDomainRigidity

end

end OAI
