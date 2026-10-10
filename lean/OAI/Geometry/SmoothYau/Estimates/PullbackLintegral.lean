import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {K : Set E} {φ : E → E} {φ' : E → E →L[ℝ] E}

theorem pullback_lintegral_le (hK : MeasurableSet K)
    (hφ : ∀ x ∈ K, HasFDerivWithinAt φ (φ' x) K x) (hinj : InjOn φ K)
    (D : ℝ≥0) (hD : ∀ x ∈ K, 1 ≤ (D : ℝ≥0∞) * ENNReal.ofReal |(φ' x).det|)
    (g : E → ℝ≥0∞) :
    ∫⁻ x in K, g (φ x) ∂μ ≤ (D : ℝ≥0∞) * ∫⁻ y, g y ∂μ := by
  calc
    _ ≤ ∫⁻ x in K, (D : ℝ≥0∞) * (ENNReal.ofReal |(φ' x).det| * g (φ x)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK] with x hx
      simpa only [one_mul, mul_assoc] using mul_le_mul' (hD x hx) (le_refl (g (φ x)))
    _ = (D : ℝ≥0∞) * ∫⁻ x in K, ENNReal.ofReal |(φ' x).det| * g (φ x) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ = (D : ℝ≥0∞) * ∫⁻ y in φ '' K, g y ∂μ := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hK hφ hinj g]
    _ ≤ (D : ℝ≥0∞) * ∫⁻ y, g y ∂μ :=
      mul_le_mul' le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)

variable {F : Type*} [NormedAddCommGroup F]

theorem pullback_eLpNorm_two_le (hK : MeasurableSet K)
    (hφ : ∀ x ∈ K, HasFDerivWithinAt φ (φ' x) K x) (hinj : InjOn φ K)
    (D : ℝ≥0) (hD : ∀ x ∈ K, 1 ≤ (D : ℝ≥0∞) * ENNReal.ofReal |(φ' x).det|)
    (g : E → F) :
    eLpNorm (g ∘ φ) 2 (μ.restrict K) ≤ (D : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm g 2 μ := by
  have hφmeas : AEMeasurable φ (μ.restrict K) :=
    (show ContinuousOn φ K from fun point hpoint =>
      (hφ point hpoint).continuousWithinAt).aemeasurable hK
  have hmap : (μ.restrict K).map φ ≤ (D : ℝ≥0∞) • μ := by
    apply Measure.le_iff.2
    intro subset hsubset
    have hbound := pullback_lintegral_le μ hK hφ hinj D hD
      (subset.indicator (fun _ => 1))
    rw [← lintegral_map' (measurable_const.indicator hsubset).aemeasurable hφmeas]
      at hbound
    simpa only [lintegral_indicator_const hsubset, one_mul, Measure.smul_apply,
      smul_eq_mul] using hbound
  calc
    _ ≤ eLpNorm g 2 ((μ.restrict K).map φ) := by
      by_cases hg : AEStronglyMeasurable g ((μ.restrict K).map φ)
      · exact (eLpNorm_map_measure hg hφmeas).ge
      · rw [eLpNorm_of_not_aestronglyMeasurable hg]
        exact le_top
    _ ≤ eLpNorm g 2 ((D : ℝ≥0∞) • μ) := eLpNorm_mono_measure g hmap
    _ ≤ _ := by simpa using eLpNorm_smul_measure_le (D : ℝ≥0∞) g 2 μ

theorem memLp_pullback_two (hK : MeasurableSet K)
    (hφ : ∀ x ∈ K, HasFDerivWithinAt φ (φ' x) K x) (hinj : InjOn φ K)
    (D : ℝ≥0) (hD : ∀ x ∈ K, 1 ≤ (D : ℝ≥0∞) * ENNReal.ofReal |(φ' x).det|)
    (g : E → F) (hg : MemLp g 2 μ)
    (hmeas : AEStronglyMeasurable (g ∘ φ) (μ.restrict K)) :
    MemLp (g ∘ φ) 2 (μ.restrict K) := by
  have hbound := pullback_eLpNorm_two_le μ hK hφ hinj D hD g
  rw [memLp_iff, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas] at hbound
  apply hbound.trans_lt
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top)
    hg.eLpNorm_lt_top

end YauCounterexamples

end

end OAI
