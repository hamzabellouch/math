import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConditionedProbeSequence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.UniformProfileConcentration

namespace OAI

/-! # Independent compact probes around a supported limiting profile

The starting sample is selected only after averaging the probes. In particular,
the retained probe mass is independent of the mass of the profile neighborhood.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A fixed finite set of probe comparisons succeeds simultaneously in
probability. No independence between the separate comparisons is needed. -/
theorem finite_bad_union_tendsto_zero
    {X J : Type*} [MeasurableSpace X] [Fintype J]
    (μ : ℕ → Measure X) (bad : ℕ → J → Set X)
    (hlim : ∀ j, Tendsto (fun n => μ n (bad n j)) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (⋃ j, bad n j)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds _
    (fun _ => zero_le) (fun n => measure_iUnion_fintype_le (μ n) (bad n))
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ => hlim j)

/-- Deterministic comparison concentration and a supported weak profile limit
supply one starting point and a compact set of good probes at shrinking
profile tolerances. This does not condition a measure on a singleton. -/
theorem exists_compact_probes_from_supported_profiles
    {X S : Type*} [MeasurableSpace X] [TopologicalSpace S]
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → S) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure S)
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (profile n)) atTop (𝓝 limitLaw))
    {f : S} (hf : f ∈ (limitLaw : Measure S).support)
    (U : ℕ → Set S) (hU : ∀ j, IsOpen (U j)) (hfU : ∀ j, f ∈ U j)
    (bad : ∀ n, ℕ → Set (X × Y n)) (hbad : ∀ n j, MeasurableSet (bad n j))
    (hdet : ∀ j, ∀ y : ∀ n, Y n,
      Tendsto (fun n => (μ : Measure X) ((fun x => (x, y n)) ⁻¹' bad n j))
        atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ ∀ᶠ n in atTop,
      ∃ x, profile n x ∈ U (k n) ∧ ∃ K : Set (Y n), IsCompact K ∧
        K ⊆ {y | (x, y) ∉ bad n (k n)} ∧ (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) K := by
  have hpos (j : ℕ) : ∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ n in atTop,
      c ≤ (μ : Measure X) (profile n ⁻¹' U j) := by
    obtain ⟨c, hc, he⟩ := eventual_positive_mass_of_supported_weak_limit hlim hf (hU j) (hfU j)
    refine ⟨ENNReal.ofReal c, ENNReal.ofReal_pos.mpr hc, he.mono ?_⟩
    intro n hn
    rw [ProbabilityMeasure.map_apply' μ (hp n).aemeasurable (hU j).measurableSet] at hn
    exact (ENNReal.ofReal_le_ofReal hn).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))
  exact eventually_exists_compact_conditioned_probes
    (fun _ => (μ : Measure X)) (fun n => (ν n : Measure (Y n)))
    (fun n j => profile n ⁻¹' U j) bad (fun n j => hp n (hU j).measurableSet) hbad hpos
    (fun j => independent_bad_probability_tendsto_zero (fun _ => μ) ν
      (fun n => bad n j) (fun n => hbad n j) (hdet j))

end PolycyclicRecognition

end

end OAI
