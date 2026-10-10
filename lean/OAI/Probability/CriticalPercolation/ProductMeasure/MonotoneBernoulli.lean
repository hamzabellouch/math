import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.Uniform01
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct

lemma uniform01_map_threshold (p : unitInterval) :
    Priority.uniform01.map (fun t : ℝ => t < p) = bitMeasure p := by
  have hm : Measurable (fun t : ℝ => t < p) := (measurable_id.lt measurable_const)
  have ht : Priority.uniform01 {t : ℝ | t < p} = ENNReal.ofReal p := by
    rw [Priority.uniform01,Measure.restrict_apply hm.setOf]
    have he : {t : ℝ | t < p} ∩ Icc 0 1 = Ico (0 : ℝ) (p : ℝ) := by
      ext t
      simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_Icc,Set.mem_Ico]
      exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h.1,h.2.le.trans p.property.2⟩⟩
    rw [he,Real.volume_Ico,sub_zero]
  have htrue : (Priority.uniform01.map (fun t : ℝ => t < p)) {True} = bitMeasure p {True} := by
    rw [Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun t : ℝ => t < p) ⁻¹' {True} = {t : ℝ | t < p} := by ext t; simp
    rw [he,ht]
    simp [bitMeasure,ENNReal.coe_nnreal_eq]
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b=True := propext (iff_true_intro hb)
    simpa only [he] using htrue
  · have he : b=False := propext (iff_false_intro hb)
    rw [he]
    have hcompl : ({True} : Set Prop)ᶜ = {False} := by ext a; simp
    rw [←hcompl,measure_compl (measurableSet_singleton _) (measure_ne_top _ _),
      measure_compl (measurableSet_singleton _) (measure_ne_top _ _),htrue]
    simp

variable {E : Type*}

def markLaw : Measure (E → ℝ) := Measure.infinitePi (fun _ : E => Priority.uniform01)

instance : IsProbabilityMeasure (markLaw (E := E)) := by
  unfold markLaw
  infer_instance

def atParameter (p : unitInterval) (u : E → ℝ) : Set E := {e | u e < p}

lemma measurable_atParameter (p : unitInterval) : Measurable (atParameter (E := E) p) :=
  Measurable.of_eval (fun edge => (measurable_pi_apply edge).lt measurable_const)

lemma markLaw_map_atParameter (p : unitInterval) :
    (markLaw (E := E)).map (atParameter p) = law (fun _ => p) := by
  have he : atParameter (E := E) p = MeasurableEquiv.setOfPred ∘ (fun u : E → ℝ => fun e => u e < p) := rfl
  rw [he,←Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    markLaw,Measure.infinitePi_map_pi (fun _ : E => Priority.uniform01)
      (f := fun _ : E => fun t : ℝ => t < (p : ℝ))
      (fun _ => measurable_id.lt measurable_const)]
  simp only [uniform01_map_threshold,law]

lemma atParameter_mono (u : E → ℝ) : Monotone (fun p : unitInterval => atParameter p u) :=
  fun _ _ hp _ he => (show _ < (_ : ℝ) from he).trans_le hp

lemma atParameter_iUnion (p : unitInterval) (q : ℕ → unitInterval)
    (hqp : ∀ n, q n ≤ p) (hq : Tendsto q atTop (𝓝 p)) (u : E → ℝ) :
    (⋃ n, atParameter (q n) u) = atParameter p u := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (fun n => atParameter_mono u (hqp n))
  · intro e he
    have he' : u e < (p : ℝ) := he
    have hq' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (p : ℝ)) :=
      continuous_subtype_val.continuousAt.tendsto.comp hq
    obtain ⟨n,hn⟩ := (hq'.eventually (lt_mem_nhds he')).exists
    exact Set.mem_iUnion.mpr ⟨n,hn⟩

def reindexMarks (e : E ≃ E) (u : E → ℝ) : E → ℝ := fun x => u (e.symm x)

lemma measurable_reindexMarks (e : E ≃ E) : Measurable (reindexMarks e) :=
  Measurable.of_eval (fun edge => measurable_pi_apply (e.symm edge))

lemma markLaw_map_reindex (e : E ≃ E) :
    (markLaw (E := E)).map (reindexMarks e) = markLaw := by
  have he : (⇑(MeasurableEquiv.piCongrLeft (fun _ : E => ℝ) e)) = reindexMarks e := by
    funext u x
    obtain ⟨y,rfl⟩ := e.surjective x
    simp [MeasurableEquiv.piCongrLeft_apply_apply,reindexMarks]
  rw [←he]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : E => Priority.uniform01) e

lemma atParameter_reindex (e : E ≃ E) (p : unitInterval) (u : E → ℝ) :
    atParameter p (reindexMarks e u) = e '' atParameter p u := by
  ext x
  obtain ⟨y,rfl⟩ := e.surjective x
  simp [atParameter,reindexMarks]

end CriticalPercolation.BernoulliProduct
end
end

end OAI
