import OAI.GroupTheory.PolycyclicRecognition.Analysis.FactorProductPacking

namespace OAI

/-! # Real cardinal bounds for lifts in a product region -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Metric
open scoped ENNReal

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]

/-- Fixed positive lifted cells convert a product-volume estimate into a
separated endpoint count. The factor projection need not be injective. -/
theorem factor_separated_card_le_product_volume (φ : D →* MulAut N)
    (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (s : Finset G) (p : G → N × D) (U : Set (N × D)) (E : Set N) (B : Set D)
    (hU : MeasurableSet U) (hU0 : (μ.prod ν) U ≠ 0) (hUtop : (μ.prod ν) U ≠ ⊤)
    (hE : μ E ≠ ⊤) (hB : ν B ≠ ⊤) {ρ : ℝ}
    (hp : ∀ x ∈ s, ι (p x).1 * κ (p x).2 = x)
    (hsmall : ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ x ∈ s, factorTranslate φ (p x) '' U ⊆ E ×ˢ B) :
    (s.card : ℝ) ≤ (μ E).toReal * (ν B).toReal / ((μ.prod ν) U).toReal := by
  have hh := factor_separated_card_mul_le φ ι κ hc μ ν hφ s p U (E ×ˢ B)
    hU hp hsmall hsep hthick
  rw [Measure.prod_prod] at hh
  have hfinite : μ E * ν B ≠ ⊤ := ENNReal.mul_ne_top hE hB
  have hr := ENNReal.toReal_mono hfinite hh
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hr
  exact (le_div_iff₀ (ENNReal.toReal_pos hU0 hUtop)).mpr hr

end PolycyclicRecognition

end

end OAI
