import OAI.NumberTheory.Jacobsthal.Probability.PhysicalMarkedRecord

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.TransitionKernels

noncomputable def rawHitRecord (a : ℕ) (r : RawMarkedHitTrace a) : CycleInputSignature :=
  lastCycleRecord (List.ofFn r.2.1) true
    (rawCycleWordSignature a (List.ofFn r.2.1++[true]).length r.2.2)

lemma rawHitRecord_measurable (a : ℕ) : Measurable (rawHitRecord a) := by
  apply measurable_sigma_family
  intro n
  apply measurable_sigma_family
  intro f
  exact (lastCycleRecord_measurable (List.ofFn f) true).comp (rawCycleWordSignature_measurable _ a)

lemma rawWord_last_physical (a : ℕ) (w : List Bool) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    ∀ᵐ s ∂rawMarkedWordKernel a (w++[true]) h,
      lastCycleRecord w true (rawCycleWordSignature a (w++[true]).length s) ∈ physicalMarkedRecord := by
  have hP : MeasurableSet {s | lastCycleRecord w true s ∈ physicalMarkedRecord} :=
    physicalMarkedRecord_measurable.preimage (lastCycleRecord_measurable w true)
  apply (ae_map_iff (rawCycleWordSignature_measurable _ a).aemeasurable hP).mp
  rw [rawMarkedWord_signature (w++[true]) a h z hz]
  exact sourceLastRecord_ae_physical w z

lemma rawFirstHit_ae_physical (a : ℕ) (v H : ℝ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    ∀ᵐ r ∂rawMarkedFirstHitKernel a v H h, rawHitRecord a r ∈ physicalMarkedRecord := by
  rw [rawMarkedFirstHitKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.sum_apply,Measure.ae_sum_iff]
  intro f
  rw [Kernel.map_apply _ (packRawMarkedHitTrace_measurable a n f)]
  apply (ae_map_iff (packRawMarkedHitTrace_measurable a n f).aemeasurable
    (physicalMarkedRecord_measurable.preimage (rawHitRecord_measurable a))).mpr
  rw [rawHitWordKernel,Kernel.restrict_apply]
  exact ae_restrict_of_ae (rawWord_last_physical a (List.ofFn f) h z hz)

lemma rawFirstHit_ae_input_window (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    ∀ᵐ r ∂rawMarkedFirstHitKernel a v H h, (rawHitRecord a r).1 ∈ Icc v (v+H) := by
  filter_upwards [rawMarkedFirstHit_ae_event a v H h] with r hr
  exact hitWordEvent_last_cost (List.ofFn r.2.1) v H _ hr

noncomputable def rawPhysicalHitEvent (a : ℕ) (v H : ℝ) : Set (RawMarkedHitTrace a) :=
  {r | rawHitRecord a r ∈ physicalMarkedRecord ∧ (rawHitRecord a r).1 ∈ Icc v (v+H)}

lemma rawPhysicalHitEvent_measurable (a : ℕ) (v H : ℝ) : MeasurableSet (rawPhysicalHitEvent a v H) :=
  (physicalMarkedRecord_measurable.preimage (rawHitRecord_measurable a)).inter
    (measurableSet_Icc.preimage (measurable_fst.comp (rawHitRecord_measurable a)))

lemma rawRegFirstHit_ae_physical (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    ∀ᵐ r ∂rawRegMarkedFirstHitKernel a v H h, r ∈ rawPhysicalHitEvent a v H := by
  rw [rawRegMarkedFirstHitKernel,stateFilter_input]
  by_cases hr : h ∈ lastRegeneration a
  · rw [ite_eq_left hr]
    let z := decodeReturnedOdd (rawLast a h)
    have hz : rawLast a h=embedOdd z := (embed_decodeReturnedOdd_of_regeneration _ hr).symm
    filter_upwards [rawFirstHit_ae_physical a v H h z hz,rawFirstHit_ae_input_window a v H h] with r hP hW
    exact ⟨hP,hW⟩
  · simp [hr]

noncomputable def rawEvenHitRecord (a : ℕ) (r : RawEvenMarkedHitTrace a) : CycleInputSignature :=
  rawHitRecord ((a+1)+2*r.1) r.2.2

lemma rawEvenHitRecord_measurable (a : ℕ) : Measurable (rawEvenHitRecord a) := by
  apply measurable_sigma_family
  intro k
  exact (rawHitRecord_measurable _).comp measurable_snd

noncomputable def rawEvenPhysicalHitEvent (a : ℕ) (v H : ℝ) : Set (RawEvenMarkedHitTrace a) :=
  {r | rawEvenHitRecord a r ∈ physicalMarkedRecord ∧ (rawEvenHitRecord a r).1 ∈ Icc v (v+H)}

lemma rawEvenPhysicalHitEvent_measurable (a : ℕ) (v H : ℝ) : MeasurableSet (rawEvenPhysicalHitEvent a v H) :=
  (physicalMarkedRecord_measurable.preimage (rawEvenHitRecord_measurable a)).inter
    (measurableSet_Icc.preimage (measurable_fst.comp (rawEvenHitRecord_measurable a)))

theorem rawEvenHit_ae_physical (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    ∀ᵐ r ∂rawEvenMarkedHitKernel a v H h, r ∈ rawEvenPhysicalHitEvent a v H := by
  rw [rawEvenMarkedHitKernel]
  apply Kernel.ae_comp_of_ae_ae (rawEvenPhysicalHitEvent_measurable a v H)
  apply Eventually.of_forall
  rintro ⟨k,y⟩
  rw [rawEvenHitContinuation,sigmaFamilyKernel_apply]
  apply (ae_map_iff (measurableSigmaMk k).aemeasurable (rawEvenPhysicalHitEvent_measurable a v H)).mpr
  have he : ((Kernel.id : Kernel (RawHistory ((a+1)+2*k)) (RawHistory ((a+1)+2*k))) ×ₖ
      rawRegMarkedFirstHitKernel ((a+1)+2*k) v H) y =
      (rawRegMarkedFirstHitKernel ((a+1)+2*k) v H y).map (Prod.mk y) := by
    ext S hS
    rw [Kernel.id_prod_apply' _ _ hS,Measure.map_apply measurable_prodMk_left hS]
  rw [he]
  apply (ae_map_iff measurable_prodMk_left.aemeasurable
    ((rawEvenPhysicalHitEvent_measurable a v H).preimage (measurableSigmaMk k))).mpr
  exact rawRegFirstHit_ae_physical _ v H y

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
