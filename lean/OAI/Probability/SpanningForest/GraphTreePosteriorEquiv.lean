import OAI.Probability.SpanningForest.IntrinsicTreeDrift
import OAI.Probability.SpanningForest.IntrinsicRelabel
import OAI.Probability.SpanningForest.WeightedTreeEquiv

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.GraphTreePosterior

theorem energy_eq_pairField (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) :
    energy T S t y = ∑ p ∈ T,
      WeightedTree.finiteField (S.image Subtype.val) t (WeightedTree.extendField y) p := by
  classical
  have hs : (∑ p ∈ S.image Subtype.val,
      if p ∈ T then WeightedTree.extendField y p - t / 2 else 0) =
      energy T S t y := by
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    simp only [WeightedTree.extendField_apply, energy]
  unfold WeightedTree.finiteField
  rw [Finset.sum_ite_mem] at hs ⊢
  rw [Finset.inter_comm] at hs
  exact hs.symm

theorem mean_eq_weightedTree (K : FiniteSubgraphCode) (e : EdgeCode)
    (S : Finset EdgeCode) (t : ℝ) (y : EdgeCode → ℝ) :
    mean K e S t y = WeightedTree.inclusion K e.1
      (WeightedTree.finiteField (S.image Subtype.val) t (WeightedTree.extendField y)) := by
  have hw (T : Finset (ℕ × ℕ)) : weight T S t y =
      WeightedTree.weight
        (WeightedTree.finiteField (S.image Subtype.val) t (WeightedTree.extendField y)) T := by
    unfold weight WeightedTree.weight
    rw [energy_eq_pairField]
  simp only [mean, numerator, partition, WeightedTree.inclusion,
    WeightedTree.numerator, WeightedTree.partition, hw]

private theorem observed_pairs_relabel (σ : Equiv ℕ ℕ) (S : Finset EdgeCode) :
    (S.image (mapEdge σ)).image Subtype.val =
      relabelEdgeSet σ (S.image Subtype.val) := by
  classical
  simp only [relabelEdgeSet, Finset.image_image]
  apply Finset.image_congr
  intro e _
  exact (relabelPair_edge σ e).symm

theorem mean_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) :
    mean (relabelFiniteSubgraph σ K) (mapEdge σ e) (S.image (mapEdge σ)) t
      (fun f => y (mapEdge σ.symm f)) = mean K e S t y := by
  classical
  rw [mean_eq_weightedTree, mean_eq_weightedTree, observed_pairs_relabel]
  apply WeightedTree.finiteTilt_edgeField_relabel σ K hK
  intro p hp
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hp
  exact f.2

theorem edgeCodes_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) :
    edgeCodes (relabelFiniteSubgraph σ K) = (edgeCodes K).image (mapEdge σ) := by
  classical
  ext f
  obtain ⟨e, rfl⟩ := mapEdge_surjective σ f
  rw [mem_edgeCodes]
  change (mapEdge σ e).1 ∈ relabelEdgeSet σ K.2 ↔ _
  rw [mem_relabelEdgeSet_iff σ K.2 hK e]
  constructor
  · intro he
    exact Finset.mem_image.mpr ⟨e, (mem_edgeCodes K e).mpr he, rfl⟩
  · intro he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    have hfe' := mapEdge_injective σ hfe
    subst f
    exact (mem_edgeCodes K e).mp hf

theorem finiteBallMean_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (e : EdgeCode) (n m : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    finiteBallMean (relabelGraph σ G) (mapEdge σ e) n m t
      (fun f => y (mapEdge σ.symm f)) = finiteBallMean G e n m t y := by
  have hK (k : ℕ) : ∀ p ∈ (Intrinsic.exhaustion G e k).2, p.1 < p.2 := by
    intro p hp
    exact ((mem_inducedCode_edges G (edgeBallCode G k e) p).mp hp).2.2.1
  simp only [finiteBallMean, Intrinsic.exhaustion_relabel,
    edgeCodes_relabel σ _ (hK n)]
  exact mean_relabel σ _ (hK m) e _ t y

theorem innerMean_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (e : EdgeCode) (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) :
    innerMean (relabelGraph σ G) (mapEdge σ e) n t
      (fun f => y (mapEdge σ.symm f)) = innerMean G e n t y := by
  simp only [innerMean, CanonicalDrift.outerLimit, finiteBallMean_relabel]

theorem drift_relabel (σ : Equiv ℕ ℕ) (G : GraphCode)
    (t : ℝ) (y : EdgeCode → ℝ) (e : EdgeCode) :
    drift (relabelGraph σ G) t (fun f => y (mapEdge σ.symm f)) (mapEdge σ e) =
      drift G t y e := by
  simp only [drift, CanonicalDrift.outerLimit, innerMean_relabel]

end Problem336.GraphTreePosterior

end

end OAI
