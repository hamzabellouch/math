import OAI.Probability.SpanningForest.AllPairObservation
import OAI.Probability.SpanningForest.GraphTreePosterior

namespace OAI

noncomputable section

namespace Problem336.AllPairObservation

attribute [local instance] Classical.propDecidable

theorem mem_edgeCodes_exhaustion_iff {G : GraphCode}
    (hf : GraphLocallyFinite G) (e a : EdgeCode) (n : ℕ) :
    a ∈ GraphTreePosterior.edgeCodes (Intrinsic.exhaustion G e n) ↔
      a ∈ observations G e n ∧ Adj G a.1.1 a.1.2 := by
  rw [GraphTreePosterior.mem_edgeCodes,
    Intrinsic.exhaustion_eq_edgeBallSubgraph G hf,
    IntrinsicExhaustion.mem_edgeBallSubgraph_edges, mem_observations]
  simp only [hf, true_and, a.2]
  tauto

theorem edgeCodes_exhaustion_eq_filter {G : GraphCode}
    (hf : GraphLocallyFinite G) (e : EdgeCode) (n : ℕ) :
    GraphTreePosterior.edgeCodes (Intrinsic.exhaustion G e n) =
      (observations G e n).filter (fun a => Adj G a.1.1 a.1.2) := by
  classical
  ext a
  simp only [Finset.mem_filter, mem_edgeCodes_exhaustion_iff hf]

theorem edgeCodes_exhaustion_subset_observations {G : GraphCode}
    (hf : GraphLocallyFinite G) (e : EdgeCode) (n : ℕ) :
    GraphTreePosterior.edgeCodes (Intrinsic.exhaustion G e n) ⊆
      observations G e n := by
  intro a ha
  exact ((mem_edgeCodes_exhaustion_iff hf e a n).mp ha).1

theorem not_adj_of_mem_observations_not_mem_edgeCodes {G : GraphCode}
    (hf : GraphLocallyFinite G) (e a : EdgeCode) (n : ℕ)
    (ha : a ∈ observations G e n)
    (hnot : a ∉ GraphTreePosterior.edgeCodes (Intrinsic.exhaustion G e n)) :
    ¬ Adj G a.1.1 a.1.2 := by
  intro hadj
  exact hnot ((mem_edgeCodes_exhaustion_iff hf e a n).mpr ⟨ha, hadj⟩)

end Problem336.AllPairObservation

end

end OAI
