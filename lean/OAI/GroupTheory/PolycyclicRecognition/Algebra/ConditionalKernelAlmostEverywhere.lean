import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConditionalKernelFiber

namespace OAI

/-! # Transferring almost-everywhere statements to conditional measures -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)

theorem factorConditionalKernel_ae {P : X → Prop}
    (hPm : MeasurableSet {x | P x}) (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ y ∂μ.map f, ∀ᵐ x ∂factorConditionalKernel μ f hf y, P x := by
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  have he : ∀ᵐ p : Y × X ∂factorGraphMeasure μ f hf, P p.2 := by
    exact (ae_map_iff hm.aemeasurable (hPm.preimage measurable_snd)).2 hP
  rw [← factorConditionalKernel_disintegrate μ f hf] at he
  exact Measure.ae_ae_of_ae_compProd he

end PolycyclicRecognition

end

end OAI
