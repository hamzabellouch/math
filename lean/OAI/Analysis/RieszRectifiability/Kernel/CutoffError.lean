import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SymmetricKernelL2
import OAI.Analysis.RieszRectifiability.Kernel.NearPairWeight
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalBilinear

namespace OAI

/-!
# Weighted fractional cutoff errors

The cutoff error weights the fractional pair energy at both endpoints. Symmetry of the
near-pair weight supports integrability and bounds for the contribution of nearby pairs.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def cutoffError {d : ℕ} (m : ℕ) (w χ : Ambient d → ℝ) (x y : Ambient d) : ℝ :=
  w x * w y * fractionalPairEnergy m χ x y

theorem nearPairWeight_swap {d : ℕ} (p : ℕ) (r : ℝ) (x y : Ambient d) :
    nearPairWeight p r (y, x) = nearPairWeight p r (x, y) := by
  classical
  have hmem : (y, x) ∈ nearPairSet r ↔ (x, y) ∈ nearPairSet r := by
    simp only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm]
  by_cases h : (x, y) ∈ nearPairSet r
  · simp only [nearPairWeight, indicator_of_mem h, indicator_of_mem (hmem.mpr h),
      inverseDistancePow, dist_comm]
  · simp only [nearPairWeight, indicator_of_notMem h,
      indicator_of_notMem (mt hmem.mp h)]

theorem near_cutoffError_integrable_and_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (L : ℝ≥0) (hχ : LipschitzWith L χ) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun q : Ambient d × Ambient d => cutoffError (p + 1) w χ q.1 q.2)
      (nearPairSet r) (μ.prod μ) ∧
      (∫ q in nearPairSet r, |cutoffError (p + 1) w χ q.1 q.2| ∂μ.prod μ) ≤
        (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ) := by
  obtain ⟨hi, hb⟩ := symmetric_weight_product_integrable_and_bound μ
    (nearPairWeight p r) (nearPairWeight_measurable p r) (nearPairWeight_nonneg p r)
    (nearPairWeight_swap p r) (nearPairWeight_section_integrable p C μ hg r hr)
    (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))
    (fun x => by simpa only [Real.norm_of_nonneg (nearPairWeight_nonneg p r _)] using!
      nearPairWeight_section_norm_bound p C μ hg r hr x) w hw hL2
  have hχm : Measurable χ := hχ.continuous.measurable
  have hm : Measurable (fun q : Ambient d × Ambient d => cutoffError (p + 1) w χ q.1 q.2) := by
    unfold cutoffError fractionalPairEnergy
    fun_prop
  have hdom (q : Ambient d × Ambient d) (hq : q ∈ nearPairSet r) :
      |cutoffError (p + 1) w χ q.1 q.2| ≤
        (L : ℝ) ^ 2 * (|w q.1 * w q.2| * nearPairWeight p r q) := by
    rw [cutoffError, abs_mul, abs_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _),
      nearPairWeight, indicator_of_mem hq]
    have h := mul_le_mul_of_nonneg_left
      (lipschitz_fractionalEnergy_bound p χ L hχ q.1 q.2) (abs_nonneg (w q.1 * w q.2))
    simpa only [inverseDistancePow, mul_left_comm] using! h
  have hI : IntegrableOn (fun q : Ambient d × Ambient d => cutoffError (p + 1) w χ q.1 q.2)
      (nearPairSet r) (μ.prod μ) := by
    apply (hi.const_mul ((L : ℝ) ^ 2)).restrict.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (nearPairSet_measurable r)] with q hq
    simpa only [Real.norm_eq_abs] using! hdom q hq
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ q in nearPairSet r,
        (L : ℝ) ^ 2 * (|w q.1 * w q.2| * nearPairWeight p r q) ∂μ.prod μ := by
      apply integral_mono_ae hI.abs (hi.const_mul ((L : ℝ) ^ 2)).restrict
      filter_upwards [ae_restrict_mem (nearPairSet_measurable r)] with q hq
      exact hdom q hq
    _ ≤ ∫ q : Ambient d × Ambient d,
        (L : ℝ) ^ 2 * (|w q.1 * w q.2| * nearPairWeight p r q) ∂μ.prod μ :=
      setIntegral_le_integral (hi.const_mul ((L : ℝ) ^ 2))
        (Filter.Eventually.of_forall fun q => by
          exact mul_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (nearPairWeight_nonneg p r q)))
    _ ≤ (L : ℝ) ^ 2 * ((2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
