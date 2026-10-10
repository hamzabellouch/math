import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

/-! # Weak subsequences under one finite dominating measure -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem probability_family_tight_of_finite_dominator {ι : Type*}
    (σ : FiniteMeasure X) (P : ι → ProbabilityMeasure X)
    (hP : ∀ k, (P k : Measure X) ≤ σ) :
    IsTightMeasureSet {((ρ : ProbabilityMeasure X) : Measure X) | ρ ∈ Set.range P} := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  obtain ⟨K,hK,hσ⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := (σ : Measure X))) ε hε
  refine ⟨K,hK,?_⟩
  rintro ν ⟨ρ,⟨k,rfl⟩,rfl⟩
  exact (hP k Kᶜ).trans (hσ σ (by simp))

theorem probability_subsequence_of_finite_dominator
    (σ : FiniteMeasure X) (P : ℕ → ProbabilityMeasure X)
    (hP : ∀ k, (P k : Measure X) ≤ σ) :
    ∃ (Q : ProbabilityMeasure X) (j : ℕ → ℕ),
      StrictMono j ∧ Tendsto (P ∘ j) atTop (𝓝 Q) := by
  have hc := isCompact_closure_of_isTightMeasureSet
    (probability_family_tight_of_finite_dominator σ P hP)
  obtain ⟨Q,_,j,hj,hlim⟩ := hc.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  exact ⟨Q,j,hj,hlim⟩

theorem countable_probability_subsequence_of_finite_dominator
    (σ : FiniteMeasure X) (P : ℕ → ℕ → ProbabilityMeasure X)
    (hP : ∀ m k, (P m k : Measure X) ≤ σ) :
    ∃ (Q : ℕ → ProbabilityMeasure X) (j : ℕ → ℕ),
      StrictMono j ∧ ∀ m, Tendsto (P m ∘ j) atTop (𝓝 (Q m)) := by
  have hc (m : ℕ) := isCompact_closure_of_isTightMeasureSet
    (probability_family_tight_of_finite_dominator σ (P m) (hP m))
  obtain ⟨Q,_,j,hj,hlim⟩ := (isCompact_pi_infinite hc).tendsto_subseq
    (fun k m => subset_closure (mem_range_self k))
  refine ⟨Q,j,hj,fun m => ?_⟩
  exact ((continuous_apply m).tendsto Q).comp hlim

end RegularPointCoordinates

end

end OAI
