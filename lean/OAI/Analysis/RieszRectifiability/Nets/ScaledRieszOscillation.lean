import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.OscillationTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem nnreal_smul_prod_same {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (c : ℝ≥0) :
    (c • μ).prod (c • ν) = c ^ 2 • μ.prod ν := by
  change ((c : ℝ≥0∞) • μ).prod ((c : ℝ≥0∞) • ν) = ((c ^ 2 : ℝ≥0) : ℝ≥0∞) • μ.prod ν
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  simp only [pow_two, ENNReal.coe_mul]

theorem rieszScalarPairing_smul_nnreal {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (c : ℝ≥0)
    (a : Ambient d) (R : ℝ) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing n (c • μ) a R e φ = (c : ℝ) ^ 2 * rieszScalarPairing n μ a R e φ := by
  unfold rieszScalarPairing
  dsimp only
  simp_rw [Measure.restrict_smul, nnreal_smul_prod_same]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_pow, smul_eq_mul]
  ring

theorem ScalarOscillationBound.smul_nnreal {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d) (A v : ℝ)
    (hosc : ScalarOscillationBound n μ a A v) (c : ℝ≥0) (hc : 0 < c) :
    ScalarOscillationBound n (c • μ) a A ((c : ℝ) ^ 2 * v) := by
  intro e he φ hφ hs hzero
  have hcR : (c : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hc).ne'
  have hz : (∫ x, φ x ∂μ) = 0 := by
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hcR
  rw [rieszScalarPairing_smul_nnreal, abs_mul, abs_of_nonneg (sq_nonneg (c : ℝ))]
  exact mul_le_mul_of_nonneg_left (hosc e he φ hφ hs hz) (sq_nonneg _)

theorem scaled_cubic_oscillation_ratio_tendsto (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 < δ j) (ht : Tendsto δ atTop (𝓝 0)) (c : ℝ≥0) :
    Tendsto (fun j => ((c : ℝ) ^ 2 * δ j ^ 3) / δ j) atTop (𝓝 0) := by
  have heq (j : ℕ) : ((c : ℝ) ^ 2 * δ j ^ 3) / δ j = (c : ℝ) ^ 2 * δ j ^ 2 := by
    field_simp [(hδ j).ne']
  simp_rw [heq]
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using! (ht.pow 2).const_mul ((c : ℝ) ^ 2)

end

end RieszRectifiability

end OAI
