import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.ScaledRieszOscillation
import OAI.Analysis.RieszRectifiability.Nets.ScaledSourceMeasure

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem setIntegral_smul_nnreal_real {d : ℕ} (μ : Measure (Ambient d))
    (s : Set (Ambient d)) (f : Ambient d → ℝ) (c : ℝ≥0) :
    (∫ x in s, f x ∂c • μ) = (c : ℝ) * ∫ x in s, f x ∂μ := by
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

theorem restricted_pair_integral_smul_nnreal {d : ℕ} (μ : Measure (Ambient d)) [SFinite μ]
    (s t : Set (Ambient d)) (f : Ambient d × Ambient d → ℝ) (c : ℝ≥0) :
    (∫ q, f q ∂((c • μ).restrict s).prod ((c • μ).restrict t)) =
      (c : ℝ) ^ 2 * ∫ q, f q ∂(μ.restrict s).prod (μ.restrict t) := by
  simp only [Measure.restrict_smul, nnreal_smul_prod_same, integral_smul_nnreal_measure,
    NNReal.smul_def, NNReal.coe_pow, smul_eq_mul]

theorem local_height_data_smul_nnreal {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (s : Set (Ambient d)) (w : Ambient d → ℝ)
    (B E : ℝ) (hw : MemLp w 2 (μ.restrict s))
    (hB : (∫ x in s, w x ^ 2 ∂μ) ≤ B)
    (hI : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n w q.1 q.2)
      ((μ.restrict s).prod (μ.restrict s)))
    (hE : (∫ q : Ambient d × Ambient d, fractionalPairEnergy n w q.1 q.2
      ∂(μ.restrict s).prod (μ.restrict s)) ≤ E) (c : ℝ≥0) :
    MemLp w 2 ((c • μ).restrict s) ∧
      (∫ x in s, w x ^ 2 ∂c • μ) ≤ (c : ℝ) * B ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n w q.1 q.2)
        (((c • μ).restrict s).prod ((c • μ).restrict s)) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy n w q.1 q.2
        ∂((c • μ).restrict s).prod ((c • μ).restrict s)) ≤ (c : ℝ) ^ 2 * E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Measure.restrict_smul]
    exact hw.smul_measure ENNReal.coe_ne_top
  · rw [setIntegral_smul_nnreal_real]
    exact mul_le_mul_of_nonneg_left hB c.coe_nonneg
  · simp only [Measure.restrict_smul, nnreal_smul_prod_same]
    exact hI.smul_measure_nnreal
  · rw [restricted_pair_integral_smul_nnreal]
    exact mul_le_mul_of_nonneg_left hE (sq_nonneg _)

theorem dyadic_source_moments_smul_nnreal {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (u : ℕ → Ambient d → ℝ)
    (δ : ℕ → ℝ) (N : ℕ → ℕ) (D b : ℝ)
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2) (c : ℝ≥0) :
    ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂c • μ j) ≤
      δ j ^ 2 * ((c : ℝ) * D) * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
  intro j l hl
  rw [setIntegral_smul_nnreal_real]
  calc
    _ ≤ (c : ℝ) * (δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2) :=
      mul_le_mul_of_nonneg_left (hsource j l hl) c.coe_nonneg
    _ = _ := by ring

theorem tendsto_setIntegral_of_positive_nnreal_smul {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (s : Set (Ambient d))
    (f : ℕ → Ambient d → ℝ) (c : ℝ≥0) (hc : 0 < c)
    (ht : Tendsto (fun j => ∫ x in s, f j x ∂c • μ j) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in s, f j x ∂μ j) atTop (𝓝 0) := by
  have hcR : (c : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hc).ne'
  have heq (j : ℕ) : (c : ℝ)⁻¹ * (∫ x in s, f j x ∂c • μ j) = ∫ x in s, f j x ∂μ j := by
    rw [setIntegral_smul_nnreal_real, ← mul_assoc, inv_mul_cancel₀ hcR, one_mul]
  simpa only [heq, mul_zero] using! ht.const_mul (c : ℝ)⁻¹

end

end RieszRectifiability

end OAI
