import OAI.Probability.PosteriorReplicas.Measures.BaseDisintegration

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_basePoint_comp {X : Type*} [MeasurableSpace X]
    {d k : ℕ} (base : BaseLaw) {A : X → Rows d k} {y : X → Labels k} {x : X → Vec d}
    (hA : Measurable A) (hy : Measurable y) (hx : Measurable x) :
    Measurable (fun z => basePoint base (A z) (y z) (x z)) := by
  have h := (measurable_basePoint (d := d) (k := k) base).comp ((hA.prodMk hy).prodMk hx)
  exact h

@[fun_prop] lemma measurable_baseDensity_comp {X : Type*} [MeasurableSpace X]
    {d k : ℕ} (base : BaseLaw) {A : X → Rows d k} {y : X → Labels k}
    (hA : Measurable A) (hy : Measurable y) :
    Measurable (fun z => baseDensity base (A z) (y z)) := by
  have h := (measurable_baseDensity (d := d) (k := k) base).comp (hA.prodMk hy)
  exact h

@[fun_prop] lemma measurable_kernelComponent_comp {X : Type*} [MeasurableSpace X]
    {d k : ℕ} {A : X → Rows d k} {x : X → Vec d}
    (hA : Measurable A) (hx : Measurable x) :
    Measurable (fun z => kernelComponent (A z) (x z)) := by
  have h := (measurable_kernelComponent (d := d) (k := k)).comp (hA.prodMk hx)
  exact h

@[fun_prop] lemma measurable_labels_comp {X : Type*} [MeasurableSpace X]
    {d k : ℕ} {A : X → Rows d k} {x : X → Vec d}
    (hA : Measurable A) (hx : Measurable x) :
    Measurable (fun z => labels (A z) (x z)) := by
  have h := (measurable_labels (d := d) (k := k)).comp (hA.prodMk hx)
  exact h
end PosteriorReplicas
end

end OAI
