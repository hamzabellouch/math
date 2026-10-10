import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Sub

namespace OAI

open MeasureTheory Filter Set Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace Invariant233.TrimmingWeakLimits

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

omit [OpensMeasurableSpace X] in

theorem testAgainstNN_add_measure (μ ν : FiniteMeasure X) (f : X →ᵇ ℝ≥0) :
    (μ + ν).testAgainstNN f = μ.testAgainstNN f + ν.testAgainstNN f := by
  simp only [← ENNReal.coe_inj, ENNReal.coe_add, FiniteMeasure.testAgainstNN_coe_eq,
    FiniteMeasure.toMeasure_add, lintegral_add_measure]

theorem tendsto_of_add_eq_of_mass_tendsto_zero {I : Type*} {l : Filter I}
    {μn βn δn : I → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μn l (𝓝 μ)) (hsplit : ∀ i, βn i + δn i = μn i)
    (hlost : Tendsto (fun i => (δn i).mass) l (𝓝 0)) :
    Tendsto βn l (𝓝 μ) := by
  apply FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.mpr
  intro f
  have hmain := FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.mp hμ f
  have hsmall := FiniteMeasure.tendsto_zero_testAgainstNN_of_tendsto_zero_mass hlost f
  have heq : (fun i => (βn i).testAgainstNN f) =
      (fun i => (μn i).testAgainstNN f - (δn i).testAgainstNN f) := by
    funext i
    rw [← hsplit i, testAgainstNN_add_measure, add_tsub_cancel_right]
  rw [heq]
  simpa only [tsub_zero] using hmain.sub hsmall

theorem tendsto_of_le_of_mass_sub_tendsto_zero {I : Type*} {l : Filter I}
    {μn βn : I → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μn l (𝓝 μ))
    (hle : ∀ i, (βn i : Measure X) ≤ (μn i : Measure X))
    (hlost : Tendsto (fun i => (μn i).mass - (βn i).mass) l (𝓝 0)) :
    Tendsto βn l (𝓝 μ) := by
  let δn : I → FiniteMeasure X := fun i =>
    ⟨(μn i : Measure X) - (βn i : Measure X), inferInstance⟩
  apply tendsto_of_add_eq_of_mass_tendsto_zero hμ (δn := δn)
  · intro i
    apply FiniteMeasure.toMeasure_injective
    change (βn i : Measure X) + ((μn i : Measure X) - (βn i : Measure X)) = _
    rw [add_comm, Measure.sub_add_cancel_of_le (hle i)]
  · have heq : (fun i => (δn i).mass) =
        (fun i => (μn i).mass - (βn i).mass) := by
      funext i
      change (((μn i : Measure X) - (βn i : Measure X)) univ).toNNReal =
        ((μn i : Measure X) univ).toNNReal - ((βn i : Measure X) univ).toNNReal
      rw [Measure.sub_apply MeasurableSet.univ (hle i), ENNReal.toNNReal_sub (measure_ne_top _ _)]
    rwa [heq]

theorem tendsto_restrict_of_compl_mass_tendsto_zero {I : Type*} {l : Filter I}
    {μn : I → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μn l (𝓝 μ)) (A : I → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hlost : Tendsto (fun i => μn i (A i)ᶜ) l (𝓝 0)) :
    Tendsto (fun i => (μn i).restrict (A i)) l (𝓝 μ) := by
  apply tendsto_of_add_eq_of_mass_tendsto_zero hμ
    (δn := fun i => (μn i).restrict (A i)ᶜ)
  · intro i
    simpa only [union_compl_self, FiniteMeasure.restrict_univ] using
      (FiniteMeasure.restrict_union (μ := μn i) disjoint_compl_right (hA i).compl).symm
  · simpa only [FiniteMeasure.restrict_mass] using hlost

end Invariant233.TrimmingWeakLimits

end OAI
