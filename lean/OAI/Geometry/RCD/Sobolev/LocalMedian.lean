import OAI.Geometry.RCD.Sobolev.MedianLevel
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Median levels for a finite working region -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

theorem exists_local_median {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {Ω : Set X} (_hΩ : MeasurableSet Ω)
    (hΩ0 : μ Ω ≠ 0) (hΩt : μ Ω ≠ ∞) (f : X → ℝ) (hf : Measurable f) :
    ∃ k : ℝ,
      μ.real Ω / 2 ≤ μ.real (Ω ∩ {x | f x ≤ k}) ∧
      μ.real Ω / 2 ≤ μ.real (Ω ∩ {x | k ≤ f x}) := by
  let ν := uniformOn μ Ω
  let := uniformOn_probability μ Ω hΩ0 hΩt
  let ρ := ν.map f
  let : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  obtain ⟨k, hk₀, hk₁⟩ := exists_probability_median ρ
  have hreal {S : Set ℝ} (hS : MeasurableSet S) (hk : (1 / 2 : ℝ≥0∞) ≤ ρ S) :
      μ.real Ω / 2 ≤ μ.real (Ω ∩ f ⁻¹' S) := by
    have hfin : μ (Ω ∩ f ⁻¹' S) ≠ ∞ := ne_top_of_le_ne_top hΩt (measure_mono inter_subset_left)
    have hρ : ρ S = (μ Ω)⁻¹ * μ (Ω ∩ f ⁻¹' S) := by
      dsimp [ρ, ν]
      rw [Measure.map_apply hf hS, uniformOn, Measure.smul_apply,
        Measure.restrict_apply (hf hS), inter_comm]
      rfl
    rw [hρ] at hk
    have hbound := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hΩ0) hfin) hk
    have hhalf : (1 / 2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
    rw [hhalf, ENNReal.toReal_mul, ENNReal.toReal_inv] at hbound
    have hpos : 0 < (μ Ω).toReal := ENNReal.toReal_pos hΩ0 hΩt
    have hm := mul_le_mul_of_nonneg_left hbound hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at hm
    simpa only [Measure.real, div_eq_mul_inv, one_mul] using hm
  exact ⟨k, hreal measurableSet_Iic hk₀, hreal measurableSet_Ici hk₁⟩

end RegularPointCoordinates

end

end OAI
