import OAI.Probability.PosteriorReplicas.Information.ConditionalKL

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma klDiv_map_leftInverse {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X → Y} {g : Y → X} (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) : klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le _ _ hf)
  have h := klDiv_map_le (μ.map f) (ν.map f) hg
  have he : g ∘ f = id := funext hgf
  simpa only [Measure.map_map hg hf, he, Measure.map_id] using h

lemma compProd_prod_right {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) [SFinite μ] (κ : Kernel Z X) [IsSFiniteKernel κ]
    (ν : Measure Y) [SFinite ν] :
    ((μ ⊗ₘ κ).prod ν).map MeasurableEquiv.prodAssoc = μ ⊗ₘ (κ ×ₖ Kernel.const Z ν) := by
  have hk : κ ×ₖ Kernel.const Z ν = κ ⊗ₖ Kernel.const (Z × X) ν := by
    ext z s hs
    rw [Kernel.prod_apply' _ _ _ hs, Kernel.compProd_apply hs]
    rfl
  rw [hk, ← Measure.compProd_const, Measure.compProd_assoc']

def attachSide {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (g : X → Z) (q : Measure (X × Y)) : Measure (Z × (X × Y)) :=
  q.map (fun z => (g z.1, z))

instance attachSide_finite {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (g : X → Z) (q : Measure (X × Y)) [IsFiniteMeasure q] :
    IsFiniteMeasure (attachSide g q) := by
  unfold attachSide
  infer_instance

lemma attachSide_probability {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {g : X → Z} (hg : Measurable g) (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    IsProbabilityMeasure (attachSide g q) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

lemma attachSide_first_pair {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {g : X → Z} (hg : Measurable g) (q : Measure (X × Y)) :
    (attachSide g q).map (fun z => (z.1,z.2.1)) = q.fst.map (fun x => (g x,x)) := by
  unfold attachSide Measure.fst
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) measurable_fst]
  rfl

lemma compProd_condKernel_fst {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (q : Measure (Z × (X × Y))) [IsFiniteMeasure q] :
    q.fst ⊗ₘ q.condKernel.fst = q.map (fun z => (z.1,z.2.1)) := by
  rw [Kernel.fst_eq, Measure.compProd_map measurable_fst, Measure.disintegrate q q.condKernel]
  rfl

lemma attachSide_conditional_reference {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    {g : X → Z} (hg : Measurable g) (q : Measure (X × Y)) [IsProbabilityMeasure q]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    let r := attachSide g q
    r.fst ⊗ₘ (r.condKernel.fst ×ₖ Kernel.const Z ν) = attachSide g (q.fst.prod ν) := by
  let := attachSide_probability hg q
  dsimp only
  rw [← compProd_prod_right, compProd_condKernel_fst, attachSide_first_pair hg]
  have hp : (q.fst.map (fun x => (g x,x))).prod ν =
      (q.fst.prod ν).map (Prod.map (fun x => (g x,x)) id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map q.fst ν
      (show Measurable (fun x => (g x,x)) by fun_prop) measurable_id
  rw [hp]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma mutualInformation_attachSide_chain {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    {g : X → Z} (hg : Measurable g) (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    let r := attachSide g q
    klDiv q (q.fst.prod q.snd) = cmi r +
      klDiv (q.map (fun z => (g z.1,z.2))) ((q.fst.map g).prod q.snd) := by
  let := attachSide_probability hg q
  dsimp only
  have h := klDiv_conditional_chain (attachSide g q) q.snd
  rw [attachSide_conditional_reference hg] at h
  have he : klDiv (attachSide g q) (attachSide g (q.fst.prod q.snd)) = klDiv q (q.fst.prod q.snd) :=
    klDiv_map_leftInverse _ _ (by fun_prop) measurable_snd (fun _ => rfl)
  rw [he] at h
  have hf : (attachSide g q).fst = q.fst.map g := by
    unfold attachSide Measure.fst
    rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_map hg measurable_fst]
    rfl
  have hy : (attachSide g q).map (fun z => (z.1,z.2.2)) =
      q.map (fun z => (g z.1,z.2)) := by
    rw [attachSide, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rwa [hf,hy] at h

end PosteriorReplicas
end

end OAI
