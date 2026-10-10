import OAI.Probability.StrongRayleigh.InnovationAdapted

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem336AdditiveD139.InnovationAdapted

variable {I : Type u_1} {Ω : Type u_2}

theorem continuous_innovation_nnreal
    (Y : ℝ≥0 → I → ℝ) (hY : ∀ i, Continuous (fun t => Y t i))
    (b : ℝ≥0 → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ≥0 × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) (i : I) :
    Continuous (fun t : ℝ≥0 => Y t i -
      ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal (Y s.toNNReal) i) := by
  have hb' : ∀ i, Measurable (fun p : ℝ × (I → ℝ) => b p.1.toNNReal p.2 i) := by
    intro j
    exact (hb j).comp (show Measurable (fun p : ℝ × (I → ℝ) =>
      (p.1.toNNReal, p.2)) by fun_prop)
  have h := continuous_innovation (fun t : ℝ => Y t.toNNReal)
    (fun j => (hY j).comp continuous_real_toNNReal)
    (fun t : ℝ => b t.toNNReal) hb' C
    (fun t y j => hbound t.toNNReal y j) i
  have h' := h.comp NNReal.continuous_coe
  change Continuous (fun t : ℝ≥0 => Y (t : ℝ).toNNReal i -
    ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal (Y s.toNNReal) i) at h'
  simpa only [Real.toNNReal_coe] using h'

theorem ae_continuous_innovation_nnreal
    [Countable I] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (Y : ℝ≥0 → Ω → I → ℝ)
    (hY : ∀ i, ∀ᵐ ω ∂μ, Continuous (fun t => Y t ω i))
    (b : ℝ≥0 → (I → ℝ) → I → ℝ)
    (hb : ∀ i, Measurable (fun p : ℝ≥0 × (I → ℝ) => b p.1 p.2 i))
    (C : ℝ) (hbound : ∀ t y i, |b t y i| ≤ C) :
    ∀ᵐ ω ∂μ, ∀ i, Continuous (fun t : ℝ≥0 => Y t ω i -
      ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal (Y s.toNNReal ω) i) := by
  filter_upwards [ae_all_iff.mpr hY] with ω hω i
  exact continuous_innovation_nnreal (fun t => Y t ω) hω b hb C hbound i

end Problem336AdditiveD139.InnovationAdapted

end

end OAI
