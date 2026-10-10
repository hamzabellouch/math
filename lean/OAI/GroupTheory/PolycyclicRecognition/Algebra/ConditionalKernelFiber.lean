import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantFactor

namespace OAI

/-! # Conditional probabilities preserve factor observables

Every measurable observable of the conditioning factor is almost surely
constant under almost every component, at its value on that component.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace X] [Nonempty X] [MeasurableEq Z]
  (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)
  (h : Y → Z) (hh : Measurable h)

include hh

/-- A factor observable retains its value under the conditional probability. -/
theorem factorConditionalKernel_fiber :
    ∀ᵐ y ∂μ.map f, ∀ᵐ x ∂factorConditionalKernel μ f hf y, h (f x) = h y := by
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  have he : ∀ᵐ p : Y × X ∂factorGraphMeasure μ f hf, h (f p.2) = h p.1 := by
    apply (ae_map_iff hm.aemeasurable
      (measurableSet_eq_fun ((hh.comp hf).comp measurable_snd) (hh.comp measurable_fst))).2
    exact Filter.Eventually.of_forall (fun _ => rfl)
  rw [← factorConditionalKernel_disintegrate μ f hf] at he
  exact Measure.ae_ae_of_ae_compProd he

end PolycyclicRecognition

end

end OAI
