import OAI.Probability.SLE.Mass.WeightedImageRandomMass

namespace OAI

/-! Pointwise conformal weight bounds imply actual image-mass bounds. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

lemma weightedImageMass_image_bounds
    {X : Type*} [MeasurableSpace X] (J : upperHalfPlane → X)
    (hJ : MeasurableEmbedding J) (μ : Measure upperHalfPlane)
    (w v : upperHalfPlane → ℝ≥0∞) (K : Set upperHalfPlane) (hK : MeasurableSet K)
    (c C : ℝ≥0∞) (hc : c ≠ ∞) (hC : C ≠ ∞)
    (hlower : ∀ z∈K, c*v z ≤ w z) (hupper : ∀ z∈K, w z ≤ C*v z) :
    c*(∫⁻ z in K, v z ∂μ) ≤ weightedImageMass J w μ (J '' K) ∧
      weightedImageMass J w μ (J '' K) ≤ C*(∫⁻ z in K, v z ∂μ) := by
  have he : weightedImageMass J w μ (J '' K) = ∫⁻ z in K, w z ∂μ := by
    rw [weightedImageMass,Measure.map_apply hJ.measurable (hJ.measurableSet_image.mpr hK),
      Set.preimage_image_eq _ hJ.injective,withDensity_apply _ hK]
  rw [he,← lintegral_const_mul' _ _ hc,← lintegral_const_mul' _ _ hC]
  exact ⟨setLIntegral_mono' hK hlower,setLIntegral_mono' hK hupper⟩

end SLEExactGauge

end

end OAI
