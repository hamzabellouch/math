import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences

namespace OAI

/-!
# Compactness and uniqueness of probability limits

Tightness and uniqueness of subsequential limits imply weak convergence,
as in the final compactness argument for prime-degree torus packets.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

/-- Tight probability measures converge if every convergent subsequence
has the specified limit. Prokhorov compactness ensures that this statement
also rules out loss of mass. -/
theorem tendsto_of_tight_of_unique_subsequential_limit
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [FirstCountableTopology (ProbabilityMeasure X)]
    (μ : ℕ → ProbabilityMeasure X) (m : ProbabilityMeasure X)
    (htight : IsTightMeasureSet {ν : Measure X | ∃ i, ν = μ i})
    (hlimit : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ ν : ProbabilityMeasure X,
      Tendsto (μ ∘ φ) atTop (𝓝 ν) → ν = m) :
    Tendsto μ atTop (𝓝 m) := by
  have hcompact : IsCompact (closure (range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext ν
    simp only [mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨ρ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨μ i, ⟨i, rfl⟩, rfl⟩
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall (fun i => subset_closure (mem_range_self i)))
  intro ν _ hν
  obtain ⟨φ, hφ, hconv⟩ := hν.tendsto_subseq
  exact hlimit φ hφ ν hconv

end DukePrimeDegree

end OAI
