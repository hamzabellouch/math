import OAI.Combinatorics.Progressions.Estimates.HaarMixedCenter
import OAI.Combinatorics.Progressions.Probability.ProductCoefficientSiteLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientProductDensity_mixed_center {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hfi : ∀ s, Integrable (f s) (ν s)) (hf0 : ∀ s x, 0 ≤ f s x)
    (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1)
    (t : K → ℤ) (φ : SiteTorus Unit U → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ (center : SiteTorus Unit U), ∫ x, φ (center + coefficientSiteTorusMap U (fun _ : Unit => t) x)
      ∂realDensityMeasure μ (coefficientProductDensity U f)
      ∂Measure.pi (fun j => ν (constantCoefficientSlotEquiv K m j).val)) =
      ∫ (c : SiteTorus Unit U), φ c ∂Measure.pi (fun j => ν (constantCoefficientSlotEquiv K m j).val) := by
  let ν₀ : ∀ j : Fin m, Measure (SubspaceArrayTorus Unit (U j)) :=
    fun j => ν (constantCoefficientSlotEquiv K m j).val
  let _ : ∀ j, IsProbabilityMeasure (ν₀ j) := fun j =>
    inferInstanceAs (IsProbabilityMeasure (ν (constantCoefficientSlotEquiv K m j).val))
  let _ : ∀ j, (ν₀ j).IsAddLeftInvariant := fun j =>
    inferInstanceAs ((ν (constantCoefficientSlotEquiv K m j).val).IsAddLeftInvariant)
  have hp := coefficientProductDensity_probability U μ ν f hfi hf0 hmass
  let _ := realDensityMeasure_probability μ (coefficientProductDensity U f) hp.1 hp.2.1 hp.2.2
  exact haar_mixed_center_integral (Measure.pi ν₀)
    (realDensityMeasure μ (coefficientProductDensity U f))
    (coefficientSiteTorusMap U (fun _ : Unit => t))
    (coefficientSiteTorusMap_continuous U _).measurable φ hφ hbound

end Erdos3.VectorPolynomial

end

end OAI
