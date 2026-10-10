import OAI.NumberTheory.Jacobsthal.Paths.OneStepHistoryReconstruction

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

local instance : MeasurableSingletonClass State := by
  constructor
  intro x
  cases x with
  | inl e => simpa only [image_singleton] using ((measurableSet_singleton e).inl_image : MeasurableSet (Sum.inl '' {e} : Set State))
  | inr o => simpa only [image_singleton] using ((measurableSet_singleton o).inr_image : MeasurableSet (Sum.inr '' {o} : Set State))

def rawReturnFirstPrefix (a : ℕ) (r : RawReturnTrace a) : RawHistory (a+1) :=
  rawPrefix (show a+1 ≤ a+2*(r.1+1) by omega) r.2

lemma rawReturnFirstPrefix_measurable (a : ℕ) : Measurable (rawReturnFirstPrefix a) := by
  apply measurable_sigma_family
  intro n
  exact rawPrefix_measurable (show a+1 ≤ a+2*(n+1) by omega)

lemma rawReturnFirstPrefix_retains (a : ℕ) (past : RawHistory a) :
    ∀ᵐ h ∂(rawReturnTraceKernel a past).map (rawReturnFirstPrefix a),
      rawPrefix (show a ≤ a+1 by omega) h=past := by
  have hm : MeasurableSet {h : RawHistory (a+1) | rawPrefix (show a ≤ a+1 by omega) h=past} :=
    (rawPrefix_measurable (show a ≤ a+1 by omega)) (measurableSet_singleton past)
  apply (ae_map_iff (rawReturnFirstPrefix_measurable a).aemeasurable hm).mpr
  rw [rawReturnTraceKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.map_apply _ (rawReturnTrace_mk_measurable a n)]
  apply (ae_map_iff (rawReturnTrace_mk_measurable a n).aemeasurable
    (hm.preimage (rawReturnFirstPrefix_measurable a))).mpr
  exact firstReturnHistory_retains_past a n past

theorem rawReturn_first_prefix (a : ℕ) (past : RawHistory a) (z : OddCost)
    (hz : rawLast a past=embedOdd z) :
    (rawReturnTraceKernel a past).map (rawReturnFirstPrefix a)=rawExtension a (a+1) past := by
  apply oneStep_measure_eq_of_last a past
    ((rawReturnTraceKernel a past).map (rawReturnFirstPrefix a)) (rawExtension a (a+1) past)
    (rawReturnFirstPrefix_retains a past) (rawExtension_retains_prefix (by omega) past)
  rw [Measure.map_map (rawLast_measurable (a+1)) (rawReturnFirstPrefix_measurable a),rawExtension_last_step]
  exact rawReturn_first_arrival a past z hz

noncomputable def firstPrefixMarkEvent (a : ℕ) (b : Bool) : Set (RawHistory (a+1)) :=
  {h | firstArrivalMark (rawLast (a+1) h)=b}

lemma firstPrefixMarkEvent_measurable (a : ℕ) (b : Bool) : MeasurableSet (firstPrefixMarkEvent a b) :=
  (firstArrivalMark_measurable.comp (rawLast_measurable (a+1))) (measurableSet_singleton b)

theorem rawBranchReturn_first_prefix (a : ℕ) (b : Bool) (past : RawHistory a) (z : OddCost)
    (hz : rawLast a past=embedOdd z) :
    (rawBranchReturnKernel a b past).map (rawReturnFirstPrefix a)=
      (rawExtension a (a+1) past).restrict (firstPrefixMarkEvent a b) := by
  rw [rawBranchReturnKernel,Kernel.restrict_apply]
  change ((rawReturnTraceKernel a past).restrict ((rawReturnFirstPrefix a) ⁻¹' firstPrefixMarkEvent a b)).map
    (rawReturnFirstPrefix a)=_
  rw [← Measure.restrict_map (rawReturnFirstPrefix_measurable a) (firstPrefixMarkEvent_measurable a b),
    rawReturn_first_prefix a past z hz]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
