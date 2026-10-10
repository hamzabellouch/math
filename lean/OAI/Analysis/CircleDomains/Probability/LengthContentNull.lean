import OAI.Analysis.CircleDomains.Modulus.LengthContent
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Vanishing one-dimensional Hausdorff content is equivalent to vanishing
Hausdorff measure. The proof retains arbitrarily small explicit covers. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma lengthContent_exists_cover {X : Type*} [EMetricSpace X] {A : Set X}
    (hA : lengthContent A = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ℕ → Set X, A ⊆ ⋃ n, T n ∧ (∑' n, ediam (T n)) < ε := by
  have hh : lengthContent A < ε := by rw [hA]; exact hε
  rw [lengthContent, OuterMeasure.ofFunction_apply] at hh
  simpa only [iInf_lt_iff, exists_prop] using hh

lemma hausdorff_one_zero_of_lengthContent_zero {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {A : Set X} (hA : lengthContent A = 0) :
    (μH[1] : Measure X) A = 0 := by
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1/(n+1:ℝ))
  have hε (n : ℕ) : 0 < ε n := ENNReal.ofReal_pos.mpr (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose T hcover hcost using fun n => lengthContent_exists_cover hA (hε n)
  have hdiam : ∀ n k, ediam (T n k) ≤ ε n := fun n k =>
    (ENNReal.le_tsum k).trans (hcost n).le
  have hh := Measure.hausdorffMeasure_le_liminf_tsum 1 A ε hεlim T
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  simp only [ENNReal.rpow_one] at hh
  apply le_antisymm _ bot_le
  calc
    _ ≤ liminf (fun n => ∑' k, ediam (T n k)) atTop := hh
    _ ≤ liminf ε atTop := liminf_le_liminf (Eventually.of_forall fun n => (hcost n).le)
    _ = 0 := hεlim.liminf_eq

end CircleDomainRigidity

end

end OAI
