import OAI.NumberTheory.Jacobsthal.Estimates.RawInitialIncreasing

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures

noncomputable def hitIncreasing (a b : ℕ) : Set (RawMarkedHitTrace b) :=
  {r | lastRawCycle b (List.ofFn r.2.1) true r.2.2 ∈ selectedIncreasing a}

lemma hitIncreasing_measurable (a b : ℕ) : MeasurableSet (hitIncreasing a b) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro f
  exact (selectedIncreasing_measurable a).preimage (lastRawCycle_measurable (List.ofFn f) b true)

lemma rawFirstHit_increasing (a b : ℕ) (v H : ℝ) (h : RawHistory b) (hh : h ∈ increasingCosts a b) :
    ∀ᵐ r ∂rawMarkedFirstHitKernel b v H h, r ∈ hitIncreasing a b := by
  rw [rawMarkedFirstHitKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.sum_apply,Measure.ae_sum_iff]
  intro f
  rw [Kernel.map_apply _ (packRawMarkedHitTrace_measurable b n f)]
  apply (ae_map_iff (packRawMarkedHitTrace_measurable b n f).aemeasurable (hitIncreasing_measurable a b)).mpr
  rw [rawHitWordKernel,Kernel.restrict_apply]
  exact ae_restrict_of_ae (lastRawCycle_increasing a (List.ofFn f) b true h hh)

lemma rawRegFirstHit_increasing (a b : ℕ) (v H : ℝ) (h : RawHistory b) (hh : h ∈ increasingCosts a b) :
    ∀ᵐ r ∂rawRegMarkedFirstHitKernel b v H h, r ∈ hitIncreasing a b := by
  rw [rawRegMarkedFirstHitKernel,stateFilter_input]
  split_ifs
  · exact rawFirstHit_increasing a b v H h hh
  · simp

noncomputable def evenHitIncreasing (a : ℕ) : Set (RawEvenMarkedHitTrace a) :=
  {r | rawEvenFinalCycle a r ∈ selectedIncreasing a}

lemma evenHitIncreasing_measurable (a : ℕ) : MeasurableSet (evenHitIncreasing a) :=
  (selectedIncreasing_measurable a).preimage (rawEvenFinalCycle_measurable a)

theorem rawEvenHit_increasing (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    ∀ᵐ r ∂rawEvenMarkedHitKernel a v H h, r ∈ evenHitIncreasing a := by
  rw [rawEvenMarkedHitKernel]
  apply Kernel.ae_comp_of_ae_ae (evenHitIncreasing_measurable a)
  filter_upwards [packedInitial_increasing a h] with r hr
  rcases r with ⟨k,y⟩
  rw [rawEvenHitContinuation,sigmaFamilyKernel_apply]
  apply (ae_map_iff (measurableSigmaMk k).aemeasurable (evenHitIncreasing_measurable a)).mpr
  have he : ((Kernel.id : Kernel (RawHistory ((a+1)+2*k)) (RawHistory ((a+1)+2*k))) ×ₖ
      rawRegMarkedFirstHitKernel ((a+1)+2*k) v H) y =
      (rawRegMarkedFirstHitKernel ((a+1)+2*k) v H y).map (Prod.mk y) := by
    ext S hS
    rw [Kernel.id_prod_apply' _ _ hS,Measure.map_apply measurable_prodMk_left hS]
  rw [he]
  exact (ae_map_iff measurable_prodMk_left.aemeasurable
    ((evenHitIncreasing_measurable a).preimage (measurableSigmaMk k))).mpr
      (rawRegFirstHit_increasing a _ v H y hr)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
