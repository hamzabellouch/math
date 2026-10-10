import OAI.Combinatorics.Progressions.Geometry.CoordinateConstantDecomposition
import OAI.Combinatorics.Progressions.Probability.CoefficientProductLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

theorem coefficientProductDensity_split_law {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s, Measurable (f s)) (hfi : ∀ s, Integrable (f s) (ν s))
    (hf0 : ∀ s x, 0 ≤ f s x) (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1) :
    (realDensityMeasure μ (coefficientProductDensity U f)).map
      (coefficientCoordinateSplit U ∘ coefficientCoordinateTorus U) =
      (Measure.pi (fun s : NonconstantCoefficientSlot K m => realDensityMeasure (ν s.val) (f s.val))).prod
        (realDensityMeasure (Measure.pi (fun j => ν (constantCoefficientSlotEquiv K m j).val))
          (fun c => ∏ j, f (constantCoefficientSlotEquiv K m j).val (c j))) := by
  let _ : ∀ s, IsProbabilityMeasure (realDensityMeasure (ν s) (f s)) :=
    fun s => realDensityMeasure_probability (ν s) (f s) (hfi s) (hf0 s) (hmass s)
  have hs := coefficientCoordinateSplit_measurePreserving U
    (fun s => realDensityMeasure (ν s) (f s))
  rw [← Measure.map_map hs.measurable (coefficientCoordinateTorus_continuous U).measurable,
    coefficientProductDensity_coordinate_law U μ ν f hf hfi hf0, hs.map_eq]
  exact congrArg (fun η =>
    (Measure.pi (fun s : NonconstantCoefficientSlot K m => realDensityMeasure (ν s.val) (f s.val))).prod η)
    (realDensityMeasure_pi (fun j => ν (constantCoefficientSlotEquiv K m j).val)
      (fun j => f (constantCoefficientSlotEquiv K m j).val)
      (fun j => hfi _) (fun j => hf0 _))

end Erdos3.VectorPolynomial

end

end OAI
