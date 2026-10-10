import OAI.Probability.PosteriorReplicas.Information.CmiKernel

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section
variable {T U V : Type*} [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

def parametricMapKernel (q : Measure U) (h : T × U → V) : Kernel T V :=
  (Kernel.id ×ₖ Kernel.const T q).map h

instance parametricMapKernel_sfinite (q : Measure U) [SFinite q]
    (h : T × U → V) : IsSFiniteKernel (parametricMapKernel q h) := by
  unfold parametricMapKernel
  infer_instance

lemma parametricMapKernel_markov (q : Measure U) [IsProbabilityMeasure q]
    (h : T × U → V) (hh : Measurable h) : IsMarkovKernel (parametricMapKernel q h) :=
  Kernel.IsMarkovKernel.map _ hh

lemma parametricMapKernel_apply (q : Measure U) [SFinite q]
    {h : T × U → V} (hh : Measurable h) (t : T) :
    parametricMapKernel q h t = q.map (fun u => h (t,u)) := by
  rw [parametricMapKernel, Kernel.map_apply _ hh, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map hh (by fun_prop)]
  rfl

lemma compProd_parametricMapKernel (μ : Measure T) [SFinite μ] (q : Measure U) [SFinite q]
    {h : T × U → V} (hh : Measurable h) :
    μ ⊗ₘ parametricMapKernel q h = (μ.prod q).map (fun z => (z.1,h z)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf, lintegral_map hf (by fun_prop),
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro t
  rw [parametricMapKernel_apply q hh, lintegral_map (by fun_prop) (by fun_prop)]
end

section RandomSide
variable {T X Y Z : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Y]

def randomSideLaw (μ : Measure T) (g : T × X → Z) (q : Measure (X × Y)) :
    Measure ((T × Z) × (X × Y)) :=
  (μ.prod q).map (fun z => ((z.1,g (z.1,z.2.1)),z.2))

instance randomSideLaw_finite (μ : Measure T) [IsFiniteMeasure μ]
    (g : T × X → Z) (q : Measure (X × Y)) [IsFiniteMeasure q] :
    IsFiniteMeasure (randomSideLaw μ g q) := by unfold randomSideLaw; infer_instance

lemma cmi_randomSideLaw (μ : Measure T) [IsFiniteMeasure μ]
    {g : T × X → Z} (hg : Measurable g) (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    cmi (randomSideLaw μ g q) = ∫⁻ t, cmi (attachSide (fun x => g (t,x)) q) ∂μ := by
  let h : T × (X × Y) → Z × (X × Y) := fun z => (g (z.1,z.2.1),z.2)
  have hh : Measurable h := by fun_prop
  let κ := parametricMapKernel q h
  have : IsMarkovKernel κ := parametricMapKernel_markov q h hh
  have he : (μ ⊗ₘ κ).map (MeasurableEquiv.prodAssoc.symm :
      T × (Z × (X × Y)) ≃ᵐ (T × Z) × (X × Y)) = randomSideLaw μ g q := by
    rw [compProd_parametricMapKernel μ q hh, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have ht (t : T) : κ t = attachSide (fun x => g (t,x)) q := by
    rw [parametricMapKernel_apply q hh]
    rfl
  have hc := cmi_compProd_assoc μ κ
  simpa only [he, ht] using hc

lemma measurable_cmi_attachSide {g : T × X → Z} (hg : Measurable g)
    (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    Measurable (fun t => cmi (attachSide (fun x => g (t,x)) q)) := by
  let h : T × (X × Y) → Z × (X × Y) := fun z => (g (z.1,z.2.1),z.2)
  have hh : Measurable h := by fun_prop
  let κ := parametricMapKernel q h
  have : IsMarkovKernel κ := parametricMapKernel_markov q h hh
  have ht (t : T) : κ t = attachSide (fun x => g (t,x)) q := by
    rw [parametricMapKernel_apply q hh]
    rfl
  simpa only [ht] using cmi_kernel_measurable κ
end RandomSide

end PosteriorReplicas
end

end OAI
