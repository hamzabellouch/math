import OAI.Probability.SpanningForest.CodedInclusion
import OAI.Probability.SpanningForest.WeightedTreeResponse
import OAI.Probability.SpanningForest.IncidenceResponse

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Classical

namespace Problem336

variable {G : GraphCode} {K : FiniteSubgraphCode}

lemma codeTransferCurrent_apply_bilinear (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (c : (ℕ × ℕ) → ℝ) (S : Finset K.2) (e f : S) :
    codeTransferCurrent hK root c S e f = c e.val.val *
      TransferCurrent.bilinear (codeWeightedLaplacian hK root (fun a => c a.val))⁻¹
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root e.val)
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root f.val) := by
  simp only [codeTransferCurrent, Matrix.mul_apply, Matrix.diagonal,
    Matrix.submatrix_apply, Matrix.transpose_apply, codeIncidence,
    Matrix.of_apply, TransferCurrent.bilinear, Matrix.mulVec, dotProduct,
    ite_mul, zero_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, id_eq]
  ring

lemma codeTransferCurrent_singleton (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (h : (ℕ × ℕ) → ℝ) (e : K.2) :
    (codeTransferCurrent hK root (fun p => Real.exp (h p)) {e}).det =
      TransferCurrent.marginal
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root)
        (fun f => h f.val) e := by
  let : Unique ({e} : Finset K.2) :=
    { default := ⟨e, by simp⟩
      uniq := by intro f; apply Subtype.ext; exact Finset.mem_singleton.mp f.property }
  rw [Matrix.det_unique, codeTransferCurrent_apply_bilinear]
  unfold TransferCurrent.marginal
  rw [TransferCurrent.laplacian_reducedGradient]
  rfl

theorem weightedTree_inclusion_eq_marginal (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (h : WeightedTree.Field) (e : K.2) :
    WeightedTree.inclusion K e.val h =
      TransferCurrent.marginal
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root)
        (fun f => h f.val) e := by
  have hr := code_tree_inclusion_ratio hK root (fun p => Real.exp (h p))
    (fun _ => Real.exp_pos _) {e}
  rw [codeTransferCurrent_singleton] at hr
  simpa only [WeightedTree.inclusion, WeightedTree.numerator, WeightedTree.partition,
    WeightedTree.weight, Real.exp_sum, SubtypeSubsetSums.forget, Finset.map_singleton,
    Function.Embedding.subtype_apply, Finset.singleton_subset_iff] using hr

theorem USTResponse.inclusion_eq_transferCurrent (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (h : USTResponse.FiniteEdge K → ℝ) (e : USTResponse.FiniteEdge K) :
    USTResponse.inclusion K h e =
      TransferCurrent.marginal
        (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root) h e := by
  let ext : WeightedTree.Field := fun p => if hp : p ∈ K.2 then h ⟨p, hp⟩ else 0
  have hext : (fun f : K.2 => ext f.val) = h := by
    funext f
    simp only [ext, dite_eq_left f.property]
  rw [← hext, WeightedTree.ustResponse_inclusion_eq]
  exact weightedTree_inclusion_eq_marginal hK root ext e

theorem USTResponse.inclusion_response_connected (hK : IsFiniteConnectedSubgraph G K)
    (a b : USTResponse.FiniteEdge K → ℝ) (e : USTResponse.FiniteEdge K)
    (D : ℝ) (hD : 0 ≤ D) (hab : ∀ f, |b f - a f| ≤ D) :
    |USTResponse.inclusion K b e - USTResponse.inclusion K a e| ≤ D / 2 := by
  obtain ⟨v, hv⟩ := hK.1
  let root : K.1 := ⟨v, hv⟩
  rw [USTResponse.inclusion_eq_transferCurrent hK root,
    USTResponse.inclusion_eq_transferCurrent hK root]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    TransferCurrent.incidence_marginal_sub_le_half (codeSource hK) (codeTarget hK) root
      (code_endpoints_connected hK) a b e D hD hab

theorem WeightedTree.inclusion_response_connected (hK : IsFiniteConnectedSubgraph G K)
    (a b : WeightedTree.Field) (e : ℕ × ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hab : ∀ f ∈ K.2, |b f - a f| ≤ D) :
    |WeightedTree.inclusion K e b - WeightedTree.inclusion K e a| ≤ D / 2 := by
  by_cases he : e ∈ K.2
  · rw [← WeightedTree.ustResponse_inclusion_eq K b ⟨e, he⟩,
      ← WeightedTree.ustResponse_inclusion_eq K a ⟨e, he⟩]
    exact USTResponse.inclusion_response_connected hK (fun f => a f.val)
      (fun f => b f.val) ⟨e, he⟩ D hD (fun f => hab f.val f.property)
  · rw [WeightedTree.inclusion_eq_zero_of_not_mem he,
      WeightedTree.inclusion_eq_zero_of_not_mem he]
    simpa using div_nonneg hD (by norm_num : (0 : ℝ) ≤ 2)

end Problem336

end

end OAI
