import Mathlib

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction
namespace ParabolicLocalization
variable {V : Type} [TopologicalSpace V]

lemma hasDerivAt_bcf_of_pointwise (u v : ℝ → (V →ᵇ ℂ)) (hv : Continuous v)
    (a b t : ℝ) (ht : t∈Ioo a b)
    (hu : ∀ s∈Ioo a b, ∀ x, HasDerivAt (fun r => u r x) (v s x) s) :
    HasDerivAt u (v t) t := by
  let w : ℝ → (V →ᵇ ℂ) := fun r => u t+∫ s in t..r, v s
  have hw : HasDerivAt w (v t) t := by
    simpa [w] using ((intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable t t)
      hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt).const_add (u t))
  apply hw.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
  apply BoundedContinuousFunction.ext
  intro x
  have hs : uIcc t r⊆Ioo a b := ordConnected_Ioo.uIcc_subset ht hr
  have hc : Continuous (fun s => v s x) := (BoundedContinuousFunction.evalCLM ℝ x).continuous.comp hv
  have he : ∫ s in t..r, v s x=u r x-u t x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs' => hu s (hs hs') x)
      (hc.intervalIntegrable t r)
  have hei := (BoundedContinuousFunction.evalCLM ℝ x).intervalIntegral_comp_comm (hv.intervalIntegrable (μ := volume) t r)
  change u r x=u t x+(∫ s in t..r, v s) x
  have he' : (∫ s in t..r, v s) x=∫ s in t..r, v s x := hei.symm
  rw [he',he]
  abel
end ParabolicLocalization

end

end OAI
