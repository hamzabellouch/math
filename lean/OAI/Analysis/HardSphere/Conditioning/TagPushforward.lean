import Mathlib
import OAI.Analysis.HardSphere.Comparison.TaggedMoment

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I X Y Z : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma taggedReference_comp (P : Measure X) [SFinite P] (E : I→Set X)
    (hE : ∀i,MeasurableSet (E i)) (κ : Kernel (I×X) Y) :
    κ ∘ₘ taggedReference P E =
      ∑i,(κ.comap (Prod.mk i) measurable_prodMk_left) ∘ₘ P.restrict (E i) := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.bind_apply hs κ.aemeasurable]
  simp only [Measure.finsetSum_apply,Measure.bind_apply hs (κ.comap _ _).aemeasurable,
    Kernel.comap_apply]
  unfold taggedReference
  rw [←lintegral_indicator (taggedEvent_measurable E hE),lintegral_prod _
    (((κ.measurable_coe hs).indicator (taggedEvent_measurable E hE)).aemeasurable),
    lintegral_count,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [←lintegral_indicator (hE i)]
  rfl

lemma taggedReference_map (P : Measure X) [SFinite P] (f : X→Y) (hf : Measurable f)
    (E : I→Set Y) (hE : ∀i,MeasurableSet (E i)) :
    (taggedReference P (fun i ↦ f ⁻¹' E i)).map (Prod.map id f)=
      taggedReference (P.map f) E := by
  unfold taggedReference
  have he : {p : I×X | p.2∈f ⁻¹' E p.1}=
      (Prod.map id f) ⁻¹' {p : I×Y | p.2∈E p.1} := rfl
  rw [he,←Measure.restrict_map (measurable_id.prodMap hf) (taggedEvent_measurable E hE)]
  have H := Measure.map_prod_map (Measure.count (α:=I)) P measurable_id hf
  rw [Measure.map_id] at H
  rw [←H]

end HardSphere.Comparison
end
end

end OAI
