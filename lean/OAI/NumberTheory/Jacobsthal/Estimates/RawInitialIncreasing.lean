import OAI.NumberTheory.Jacobsthal.Paths.RawIncreasingPrefix

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures

noncomputable def continuationIncreasing (a b : ℕ) : Set (RawContinuationTrace b) :=
  {r | Sum.elim (fun h => h ∈ increasingCosts a b) (fun r => r ∈ returnIncreasing a b) r}

lemma continuationIncreasing_measurable (a b : ℕ) : MeasurableSet (continuationIncreasing a b) := by
  apply measurableSet_sum_iff.mpr
  constructor
  · exact increasingCosts_measurable a b
  · exact returnIncreasing_measurable a b

lemma rawContinuation_increasing (a b : ℕ) (h : RawHistory b) (hh : h ∈ increasingCosts a b) :
    ∀ᵐ r ∂rawContinuationKernel b h, r ∈ continuationIncreasing a b := by
  rw [rawContinuationKernel,Kernel.piecewise_apply]
  split_ifs
  · rw [Kernel.map_apply _ measurable_inl]
    apply (ae_map_iff measurable_inl.aemeasurable (continuationIncreasing_measurable a b)).mpr
    change ∀ᵐ y ∂Measure.dirac h, y ∈ increasingCosts a b
    exact (ae_dirac_iff (increasingCosts_measurable a b)).mpr hh
  · rw [Kernel.map_apply _ measurable_inr]
    exact (ae_map_iff measurable_inr.aemeasurable (continuationIncreasing_measurable a b)).mpr
      (rawReturn_increasing a b h hh)

noncomputable def packedIncreasing (a : ℕ) : Set (RawInitialPackedTrace a) :=
  {r | r.2 ∈ increasingCosts a ((a+1)+2*r.1)}

lemma packedIncreasing_measurable (a : ℕ) : MeasurableSet (packedIncreasing a) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro k
  exact increasingCosts_measurable a _

lemma packRawInitialEven_increasing (a : ℕ) (r : RawInitialEvenTrace a)
    (hr : r ∈ continuationIncreasing a (a+1)) : packRawInitialEven a r ∈ packedIncreasing a := by
  cases r with
  | inl y => exact hr
  | inr y => exact hr

theorem packedInitial_increasing (a : ℕ) (h : RawHistory a) :
    ∀ᵐ r ∂packedInitialKernel a h, r ∈ packedIncreasing a := by
  rw [packedInitialKernel,Kernel.map_apply _ (packRawInitialEven_measurable a)]
  apply (ae_map_iff (packRawInitialEven_measurable a).aemeasurable (packedIncreasing_measurable a)).mpr
  have hs : ∀ᵐ r ∂rawInitialEvenKernel a h, r ∈ continuationIncreasing a (a+1) := by
    rw [rawInitialEvenKernel]
    apply Kernel.ae_comp_of_ae_ae (continuationIncreasing_measurable a (a+1))
    filter_upwards [rawExtension_increasingCosts a (a+1) h] with y hy
    exact rawContinuation_increasing a (a+1) y hy
  filter_upwards [hs] with r hr
  exact packRawInitialEven_increasing a r hr

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
