import OAI.Analysis.CircleDomains.Sobolev.LipschitzIntervalPaths
import OAI.Analysis.CircleDomains.Modulus.BilipschitzPathCost

namespace OAI

/-! An actual interval in a chart with a Lipschitz inverse coordinate has
finite weighted path cost whenever its image has finite weighted Hausdorff length. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem intervalChartPath_antilipschitz (φ : ℝ → X) (ψ : X → ℝ)
    {a b : ℝ} (hab : a < b) {L K : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) {U : Set X}
    (hK : LipschitzOnWith K ψ U) (hU : MapsTo φ (Icc a b) U)
    (hinv : ∀u ∈ Icc a b, ψ (φ u) = u) :
    AntilipschitzWith ((nndist a b)⁻¹ * K) (intervalChartPath φ hab.le hL).val := by
  apply AntilipschitzWith.of_le_mul_dist
  intro s t
  have hs := realIntervalPath_mem hab.le s
  have ht := realIntervalPath_mem hab.le t
  change dist s t ≤ _ * dist (φ (realIntervalPath a b s)) (φ (realIntervalPath a b t))
  calc
    dist s t ≤ ((nndist a b)⁻¹ : ℝ≥0) *
        dist (realIntervalPath a b s) (realIntervalPath a b t) :=
      (realIntervalPath_antilipschitz hab.ne).le_mul_dist s t
    _ = ((nndist a b)⁻¹ : ℝ≥0) *
        dist (ψ (φ (realIntervalPath a b s))) (ψ (φ (realIntervalPath a b t))) := by
      rw [hinv _ hs, hinv _ ht]
    _ ≤ ((nndist a b)⁻¹ : ℝ≥0) *
        (K * dist (φ (realIntervalPath a b s)) (φ (realIntervalPath a b t))) := by
      exact mul_le_mul_of_nonneg_left (hK.dist_le_mul _ (hU hs) _ (hU ht)) (by positivity)
    _ = _ := by simp only [NNReal.coe_mul, mul_assoc]

theorem intervalChartPath_range (φ : ℝ → X) {a b : ℝ} (hab : a < b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) :
    range (intervalChartPath φ hab.le hL).val = φ '' Icc a b := by
  change range (φ ∘ realIntervalPath a b) = _
  rw [range_comp, range_realIntervalPath hab]

variable [MeasurableSpace X] [BorelSpace X]

theorem intervalChartPath_cost_lt_top (φ : ℝ → X) (ψ : X → ℝ)
    {a b : ℝ} (hab : a < b) {L K : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hL0 : L ≠ 0) {U : Set X}
    (hK : LipschitzOnWith K ψ U) (hU : MapsTo φ (Icc a b) U)
    (hinv : ∀u ∈ Icc a b, ψ (φ u) = u)
    {S : Set X} (hS : φ '' Icc a b ⊆ S) (g : X → ℝ≥0∞)
    (hfinite : (∫⁻x in S, g x ∂(μH[1] : Measure X)) < ∞) :
    (∫⁻x, g x ∂pathOccupation (intervalChartPath φ hab.le hL)) < ∞ := by
  apply bilipschitz_pathCost_lt_top _ (intervalChartPath_lipschitz φ hab.le hL)
    (mul_ne_zero hL0 (by simpa only [ne_eq, nndist_eq_zero] using hab.ne))
    (intervalChartPath_antilipschitz φ ψ hab hL hK hU hinv)
  apply lt_of_le_of_lt (lintegral_mono_set (μ := (μH[1] : Measure X)) ?_) hfinite
  rw [intervalChartPath_range φ hab hL]
  exact hS

end CircleDomainRigidity

end

end OAI
