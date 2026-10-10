import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ReferenceCharge

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.FiniteMessage
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal
variable {d N : ℕ}
lemma fibre_measurable (v : Fin N) : MeasurableSet {x : Ambient d × Fin N | x.2=v} :=
  measurable_snd (measurableSet_singleton v)
lemma sum_restrict_fibres (μ : Measure (Ambient d × Fin N)) :
    (∑ v : Fin N,μ.restrict {x|x.2=v})=μ := by
  have hu : (⋃ v : Fin N,{x : Ambient d × Fin N|x.2=v})=univ := by ext x; simp
  have hd : Pairwise (Disjoint on (fun v : Fin N => {x : Ambient d × Fin N|x.2=v})) := by
    intro v w hvw
    change Disjoint {x : Ambient d × Fin N | x.2=v} {x|x.2=w}
    rw [Set.disjoint_left]
    intro x hx hxw
    exact hvw (hx.symm.trans hxw)
  have hh := Measure.restrict_iUnion (μ := μ) hd (fun v => fibre_measurable v)
  rw [hu,Measure.restrict_univ] at hh
  simpa only [Measure.sum_fintype] using hh.symm
lemma component_le (μ : Measure (Ambient d × Fin N)) (v : Fin N) : component μ v ≤ μ.map Prod.fst :=
  Measure.map_mono (Measure.restrict_le_self) measurable_fst
lemma sum_components (μ : Measure (Ambient d × Fin N)) : (∑ v,component μ v)=μ.map Prod.fst := by
  rw [← sum_restrict_fibres μ,Measure.map_finset_sum]
  · congr 1
    ext v
    rw [sum_restrict_fibres]
    rfl
  · exact measurable_fst.aemeasurable
lemma component_finite (μ : Measure (Ambient d × Fin N)) [IsFiniteMeasure μ] (v : Fin N) :
    IsFiniteMeasure (component μ v) := by unfold component; infer_instance
lemma component_apply (μ : Measure (Ambient d × Fin N)) (v : Fin N) (s : Set (Ambient d)) (hs : MeasurableSet s) :
    component μ v s=μ ((Prod.fst ⁻¹' s) ∩ {x|x.2=v}) := by
  rw [component,Measure.map_apply measurable_fst hs,Measure.restrict_apply (measurable_fst hs)]
lemma component_univ (μ : Measure (Ambient d × Fin N)) (v : Fin N) :
    component μ v univ=μ {x|x.2=v} := by simp [component_apply μ v univ MeasurableSet.univ]
lemma component_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure (Ambient d × Fin N)) (v : Fin N) :
    component (∑ i ∈ s,μ i) v=∑ i ∈ s,component (μ i) v := by
  ext t ht
  simp only [component_apply _ _ _ ht,Measure.finsetSum_apply]
lemma component_graph (ρ : Measure (Ambient d)) (w v : Fin N) :
    component (ρ.map (fun s => (s,w))) v=if w=v then ρ else 0 := by
  ext t ht
  rw [component_apply _ _ _ ht,Measure.map_apply (show Measurable (fun s : Ambient d => (s,w)) from measurable_id.prodMk measurable_const)
    ((measurable_fst ht).inter (fibre_measurable v))]
  by_cases h : w=v
  · simp only [ite_eq_left h]
    congr 1
    ext s
    simp [h]
  · simp [h]
lemma lintegral_component (μ : Measure (Ambient d × Fin N)) (v : Fin N)
    (f : Ambient d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s,f s ∂component μ v)=∫⁻ x in {x|x.2=v},f x.1 ∂μ := by
  exact lintegral_map hf measurable_fst
lemma lintegral_split (μ : Measure (Ambient d × Fin N))
    (f : Ambient d × Fin N → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x,f x ∂μ)=∑ v : Fin N,∫⁻ s,f (s,v) ∂component μ v := by
  conv_lhs => rw [← sum_restrict_fibres μ]
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro v _
  rw [lintegral_component μ v (fun s => f (s,v)) (hf.comp (measurable_id.prodMk measurable_const))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (fibre_measurable v)] with x hx
  change x.2=v at hx
  exact congrArg f (Prod.ext rfl hx)
end KernelPotential.FiniteMessage

end OAI
