import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConditionalKernelFiber
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CountableMeasureTests

namespace OAI

/-! # Consistency of conditional component measures

A conditional probability is concentrated where its own conditional probability
has the same value. Only a countable determining family of measurable sets is
used to obtain one simultaneous almost-everywhere statement.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory MeasurableSpace

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)

/-- Equality of measures, simultaneously on almost every fiber. -/
theorem factorConditionalKernel_consistent :
    ∀ᵐ y ∂μ.map f, ∀ᵐ x ∂factorConditionalKernel μ f hf y,
      factorConditionalKernel μ f hf (f x) = factorConditionalKernel μ f hf y := by
  have h (I : Finset ℕ) := factorConditionalKernel_fiber μ f hf
    (fun y => factorConditionalKernel μ f hf y (finiteMeasureTest X I))
    ((factorConditionalKernel μ f hf).measurable_coe (measurableSet_finiteMeasureTest X I))
  filter_upwards [ae_all_iff.2 h] with y hy
  filter_upwards [ae_all_iff.2 hy] with x hx
  exact measure_eq_of_finiteMeasureTests X _ _ hx

variable {G : Type*} [Group G] [MulAction G X]

/-- The same consistency statement on the original action space. -/
theorem invariantConditionalMeasures_consistent :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂invariantConditionalMeasures (G := G) μ x,
      invariantConditionalMeasures (G := G) μ y = invariantConditionalMeasures (G := G) μ x := by
  have h := factorConditionalKernel_consistent μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X)
  exact ae_of_ae_map (measurable_invariantFactorMap G X).aemeasurable h

end PolycyclicRecognition

end

end OAI
