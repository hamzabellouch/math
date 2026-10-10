import OAI.Combinatorics.InfiniteMatroid.CoveringReduction
import OAI.Combinatorics.InfiniteMatroid.PairDuality
import OAI.Combinatorics.InfiniteMatroid.Main

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

theorem separate_covering_packing_counterexamples :
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ CoveringConjectureFor F M) ∧
    (∃ (F : Set E) (M : Bool → Matroid E),
      (∀ i, (M i).E = F) ∧ ¬ PackingConjectureFor F M) := by
  obtain ⟨_, _, M₀, M₁, hE₀, hE₁, _, _, _, hno⟩ := main
  let M : Bool → Matroid E := fun i ↦ if i then M₁ else M₀
  have hg : ∀ i, (M i).E = univ := by
    intro i
    cases i <;> simp [M, hE₀, hE₁]
  have hn : ¬ HasPackingCovering (M false) (M true) := hno
  obtain ⟨C, N, hN, hnc, hcond⟩ := separate_covering_of_no_packingCovering hg hn
  refine ⟨⟨C, N, hN, fun h ↦ hnc (h.mpr hcond)⟩,
    ⟨C, fun i ↦ (N i).dual, ?_, ?_⟩⟩
  · simpa only [Matroid.dual_ground] using hN
  · exact separate_packing_of_covering_counterexample hN hnc hcond

end InfiniteMatroidCounterexample

end OAI
