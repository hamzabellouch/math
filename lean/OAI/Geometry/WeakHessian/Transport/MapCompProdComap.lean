import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessianTransport
variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]

lemma map_compProd_comap (μ : Measure A) [SFinite μ] (κ : Kernel Z B)
    [IsSFiniteKernel κ] (f : A → Z) (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (fun p : A×B => (f p.1,p.2)) = μ.map f ⊗ₘ κ := by
  have hF : Measurable (fun p : A×B => (f p.1,p.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hF hs,
    Measure.compProd_apply (hs.preimage hF),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

lemma exists_fiber_gluing [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A → Z) (g : B → Z) (hf : Measurable f) (hg : Measurable g)
    (hpush : μ.map f = ν.map g) :
    ∃ q : Measure (A×B), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      q.map (fun p : A×B => (f p.1,p.2)) = ν.map (fun b => (g b,b)) := by
  let κ := condDistrib (id : B → B) g ν
  let q := μ ⊗ₘ κ.comap f hf
  have hmap : q.map (fun p : A×B => (f p.1,p.2)) = ν.map (fun b => (g b,b)) := by
    rw [map_compProd_comap μ κ f hf, hpush]
    exact compProd_map_condDistrib hg.aemeasurable aemeasurable_id
  refine ⟨q, inferInstance, Measure.fst_compProd μ (κ.comap f hf), ?_, hmap⟩
  have hF : Measurable (fun p : A×B => (f p.1,p.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hG : Measurable (fun b : B => (g b,b)) := hg.prodMk measurable_id
  have H := congrArg (fun r : Measure (Z×B) => r.map Prod.snd) hmap
  rw [Measure.map_map measurable_snd hF,
      Measure.map_map measurable_snd hG] at H
  simpa only [Function.comp_def, Measure.map_id'] using H

lemma exists_fiber_gluing_supported [StandardBorelSpace B] [Nonempty B]
    [StandardBorelSpace Z]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A → Z) (g : B → Z) (hf : Measurable f) (hg : Measurable g)
    (hpush : μ.map f = ν.map g) :
    ∃ q : Measure (A×B), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      ∀ᵐ p ∂q, f p.1 = g p.2 := by
  obtain ⟨q,hqp,hq0,hq1,hq⟩ := exists_fiber_gluing μ ν f g hf hg hpush
  refine ⟨q,hqp,hq0,hq1,?_⟩
  have hfull : ∀ᵐ p ∂ν.map (fun b => (g b,b)), p.1 = g p.2 := by
    apply (ae_map_iff (hg.prodMk measurable_id).aemeasurable ?_).mpr
    · exact ae_of_all _ (fun _ => rfl)
    · exact measurableSet_eq_fun measurable_fst (hg.comp measurable_snd)
  rw [← hq] at hfull
  have hF : Measurable (fun p : A×B => (f p.1,p.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  exact (ae_map_iff hF.aemeasurable
    (measurableSet_eq_fun measurable_fst (hg.comp measurable_snd))).mp hfull

end WeakHessianTransport

end
end InlinedFile0

end OAI
