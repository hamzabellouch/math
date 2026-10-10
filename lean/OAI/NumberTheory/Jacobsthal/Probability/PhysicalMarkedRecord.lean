import OAI.NumberTheory.Jacobsthal.Renewal.LastCycleRecord

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels

noncomputable def recordFirst (c : CycleInputSignature) : CostState := c.2.2.1
lemma recordFirst_measurable : Measurable recordFirst :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)

noncomputable def physicalMarkedRecord : Set CycleInputSignature :=
  {c | firstArrivalMark (recordFirst c)=true ∧
    (recordFirst c).2=c.1+cost (stateRatio (recordFirst c).1)}

lemma physicalMarkedRecord_measurable : MeasurableSet physicalMarkedRecord :=
  ((firstArrivalMark_measurable.comp recordFirst_measurable) (measurableSet_singleton true)).inter
    (measurableSet_eq_fun (measurable_snd.comp recordFirst_measurable)
      (measurable_fst.add (cost_measurable.comp (stateRatio_measurable.comp
        (measurable_fst.comp recordFirst_measurable)))))

lemma source_record_physical (z : OddCost) (y : SourceCycleWitness) (hy : sourceMark y.1=true) :
    sourceCycleInputSignature z y ∈ physicalMarkedRecord := by
  exact ⟨hy,rfl⟩

lemma physicalMarkedRecord_witness {c : CycleInputSignature} (hc : c ∈ physicalMarkedRecord) :
    ∃ t : EvenState, 209/100 ≤ t.1 ∧ t.1 ≤ 213/100 ∧
      recordFirst c=(Sum.inl t,c.1+cost t.1) := by
  rcases hc with ⟨hm,hc⟩
  cases he : (recordFirst c).1 with
  | inl t =>
    have ht : sourceMark t=true := by simpa only [firstArrivalMark,he,Sum.elim_inl] using hm
    have hb : 209/100 ≤ t.1 ∧ t.1 ≤ 213/100 := by simpa [sourceMark] using ht
    refine ⟨t,hb.1,hb.2,Prod.ext he ?_⟩
    simpa only [he,stateRatio,Sum.elim_inl] using hc
  | inr t => simp [firstArrivalMark,he] at hm

lemma sourceRecord_ae_physical (z : OddCost) :
    ∀ᵐ c ∂sourceRecordKernel true z, c ∈ physicalMarkedRecord := by
  rw [sourceRecordKernel_apply]
  apply (ae_map_iff (sourceCycleInputSignature_measurable.comp measurable_prodMk_left).aemeasurable
    physicalMarkedRecord_measurable).mpr
  rw [sourceBranchWitnessKernel,Kernel.restrict_apply]
  filter_upwards [ae_restrict_mem ((sourceMark_measurable.comp measurable_fst) (measurableSet_singleton true))] with y hy
  exact source_record_physical z y hy

lemma sourceLastRecord_ae_physical (w : List Bool) (z : OddCost) :
    ∀ᵐ s ∂sourceMarkedWordKernel (w++[true]) z, lastCycleRecord w true s ∈ physicalMarkedRecord := by
  apply (ae_map_iff (lastCycleRecord_measurable w true).aemeasurable physicalMarkedRecord_measurable).mp
  rw [sourceLastRecord_law]
  exact Kernel.ae_comp_of_ae_ae physicalMarkedRecord_measurable (Eventually.of_forall sourceRecord_ae_physical)

lemma hitWordEvent_last_cost (w : List Bool) (v H : ℝ) :
    ∀ s ∈ hitWordEvent w v H, (lastCycleRecord w true s).1 ∈ Icc v (v+H) := by
  induction w with
  | nil => intro s hs; exact hs
  | cons b w ih => intro s hs; exact ih s.2 hs.2

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
