import Mathlib

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open MeasureTheory

noncomputable def densityPush {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (φ : α → β) (ρ : α → ℝ) : Measure β := by
  classical
  exact if AEMeasurable φ (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) then
    Measure.map φ (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) else 0

lemma densityPush_eq_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) (ρ : α → ℝ) :
    densityPush μ φ ρ = Measure.map φ (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  exact ite_eq_left hφ.aemeasurable

lemma densityPush_finite {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (φ : α → β) {ρ : α → ℝ} (hρ : Integrable ρ μ) :
    IsFiniteMeasure (densityPush μ φ ρ) := by
  let := isFiniteMeasure_withDensity_ofReal hρ.hasFiniteIntegral
  unfold densityPush
  split
  · exact MeasureTheory.Measure.isFiniteMeasure_map _ _
  · infer_instance

lemma integral_densityPush {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) {ρ : α → ℝ}
    (hρ : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    {b : β → ℝ} (hb : Continuous b) :
    (∫ x, b x ∂densityPush μ φ ρ) = ∫ z, ρ z*b (φ z) ∂μ := by
  rw [densityPush_eq_map μ hφ,integral_map hφ.aemeasurable hb.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ0] with z hz
  simp only [ENNReal.toReal_ofReal hz,smul_eq_mul]

lemma integral_densityPush_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) {ρ : α → ℝ}
    (hρ : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    {b : β → ℝ} (hb : Measurable b) :
    (∫ x, b x ∂densityPush μ φ ρ) = ∫ z, ρ z*b (φ z) ∂μ := by
  rw [densityPush_eq_map μ hφ,integral_map hφ.aemeasurable hb.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ0] with z hz
  simp only [ENNReal.toReal_ofReal hz,smul_eq_mul]

section BorelChartTests
variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
lemma integrable_weighted_comp (μ : Measure Z) {φ : Z → X} (hφ : Measurable φ)
    {w : Z → ℝ} (hw : Integrable w μ) {b : X → ℝ}
    (hb : Measurable b) (hB : ∃ M : ℝ, ∀ x, |b x| ≤ M) :
    Integrable (fun z => w z * b (φ z)) μ := by
  obtain ⟨M,hM⟩ := hB
  exact hw.mul_bdd (hb.comp hφ).aestronglyMeasurable
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hM (φ z))

end BorelChartTests
end SharpIntegralFillings
end

end OAI
