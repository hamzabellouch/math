import OAI.Probability.SpanningForest.CodeLaplacian
import OAI.Probability.SpanningForest.CodedIncidenceMinors
import OAI.Probability.SpanningForest.SubtypeSubsetSums

namespace OAI

noncomputable section

open scoped BigOperators Matrix
open Classical

namespace Problem336

variable {G : GraphCode} {K : FiniteSubgraphCode}

def codeIncidence (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    Matrix {v : K.1 // v ≠ root} K.2 ℝ :=
  (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root).transpose

theorem spanningTrees_eq_powersetCard_filter (root : K.1) :
    spanningTrees K = (K.2.powersetCard (Fintype.card {v : K.1 // v ≠ root})).filter
      (TreeOn K) := by
  have hc : Fintype.card {v : K.1 // v ≠ root} = K.1.card - 1 := by
    rw [Fintype.card_subtype_compl (fun v : K.1 => v = root),
      Fintype.card_coe, Fintype.card_subtype_eq]
  ext T
  simp only [spanningTrees, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨hsub, ht⟩
    exact ⟨⟨hsub, by rw [hc]; have := ht.2.1; omega⟩, ht⟩
  · rintro ⟨⟨hsub, _⟩, ht⟩
    exact ⟨hsub, ht⟩

theorem codeIncidence_minor_sq (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (s : CauchyBinet.ColumnSets {v : K.1 // v ≠ root} K.2) :
    (CauchyBinet.columnMinor (codeIncidence hK root) s).det ^ 2 =
      if TreeOn K (SubtypeSubsetSums.forget K.2 s.val) then 1 else 0 :=
  FiniteIncidence.columnMinor_det_sq_eq_treeOn hK root s

theorem codeIncidence_weighted_partition {R : Type*} [CommRing R]
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (f : ℝ →+* R) (c : (ℕ × ℕ) → R) :
    Matrix.det ((codeIncidence hK root).map f *
      Matrix.diagonal (fun e : K.2 => c e.val) *
      ((codeIncidence hK root).map f).transpose) =
      ∑ T ∈ spanningTrees K, ∏ p ∈ T, c p := by
  rw [CauchyBinet.det_weighted_gram_map_eq_sum_filter
    (codeIncidence hK root) f (fun e : K.2 => c e.val)
    (fun s => TreeOn K (SubtypeSubsetSums.forget K.2 s))
    (codeIncidence_minor_sq hK root)]
  calc
    _ = ∑ s ∈ ((Finset.univ : Finset K.2).powersetCard
          (Fintype.card {v : K.1 // v ≠ root})).filter
          (fun s => TreeOn K (SubtypeSubsetSums.forget K.2 s)),
        ∏ p ∈ SubtypeSubsetSums.forget K.2 s, c p := by
      apply Finset.sum_congr rfl
      intro s _
      exact (SubtypeSubsetSums.prod_forget K.2 s c).symm
    _ = ∑ T ∈ (K.2.powersetCard
          (Fintype.card {v : K.1 // v ≠ root})).filter (TreeOn K),
        ∏ p ∈ T, c p :=
      SubtypeSubsetSums.sum_powersetCard_filter K.2 _ (TreeOn K) (fun T => ∏ p ∈ T, c p)
    _ = _ := by rw [← spanningTrees_eq_powersetCard_filter root]

theorem codeWeightedLaplacian_tree_partition
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) :
    (codeWeightedLaplacian hK root (fun e => c e.val)).det =
      ∑ T ∈ spanningTrees K, ∏ p ∈ T, c p := by
  simpa only [RingHom.coe_id, Matrix.map_id, codeIncidence, Matrix.transpose_transpose,
    codeWeightedLaplacian, ReducedLaplacian.weightedLaplacian] using
    codeIncidence_weighted_partition hK root (RingHom.id ℝ) c

theorem codeWeightedLaplacian_det_eq_tree_count
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    (codeWeightedLaplacian hK root (fun _ => 1)).det = (spanningTrees K).card := by
  simpa using codeWeightedLaplacian_tree_partition hK root (fun _ => 1)

end Problem336

end

end OAI
