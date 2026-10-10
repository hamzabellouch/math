import OAI.Probability.SpanningForest.CodedMatrixTree
import OAI.Probability.SpanningForest.MarkedGram
import OAI.Probability.SpanningForest.InclusionPolynomial

namespace OAI

noncomputable section

open scoped BigOperators Polynomial Matrix
open Classical Polynomial

namespace Problem336

variable {G : GraphCode} {K : FiniteSubgraphCode}

def codeTransferCurrent (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) (S : Finset K.2) : Matrix S S ℝ :=
  Matrix.diagonal (fun e : S => c e.val.val) *
    ((codeIncidence hK root).submatrix id (Subtype.val : S → K.2)).transpose *
      (codeWeightedLaplacian hK root (fun e => c e.val))⁻¹ *
      (codeIncidence hK root).submatrix id (Subtype.val : S → K.2)

theorem code_tree_marker_identity (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) (hc : ∀ e : K.2, 0 < c e.val) (S : Finset K.2) :
    (∑ T ∈ spanningTrees K, C (∏ p ∈ T, c p) *
      (1 + (X : ℝ[X])) ^ (T ∩ SubtypeSubsetSums.forget K.2 S).card) =
      C (∑ T ∈ spanningTrees K, ∏ p ∈ T, c p) *
        (1 + (X : ℝ[X]) • (codeTransferCurrent hK root c S).map C).det := by
  have hA : IsUnit ((codeIncidence hK root) *
      Matrix.diagonal (fun e : K.2 => c e.val) * (codeIncidence hK root).transpose).det := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [codeIncidence, Matrix.transpose_transpose, codeWeightedLaplacian,
      ReducedLaplacian.weightedLaplacian] using
      codeWeightedLaplacian_det_ne_zero hK root (fun e => c e.val) hc
  have hp := codeIncidence_weighted_partition hK root C
    (fun p => C (c p) *
      (if p ∈ SubtypeSubsetSums.forget K.2 S then 1 + (X : ℝ[X]) else 1))
  simp only [SubtypeSubsetSums.mem_forget] at hp
  have hm := Determinantal.det_marked_weighted_gram
    (codeIncidence hK root) (fun e : K.2 => c e.val) hA S
  rw [hp] at hm
  have hZ : ((codeIncidence hK root) * Matrix.diagonal (fun e : K.2 => c e.val) *
      (codeIncidence hK root).transpose).det =
      ∑ T ∈ spanningTrees K, ∏ p ∈ T, c p := by
    exact codeWeightedLaplacian_tree_partition hK root c
  rw [hZ] at hm
  simpa only [Determinantal.prod_marked_weights, ← map_prod,
    codeTransferCurrent, codeWeightedLaplacian, ReducedLaplacian.weightedLaplacian,
    codeIncidence, Matrix.transpose_transpose, Matrix.mul_assoc] using hm

theorem code_tree_inclusion_mass (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) (hc : ∀ e : K.2, 0 < c e.val) (S : Finset K.2) :
    (∑ T ∈ (spanningTrees K).filter (fun T => SubtypeSubsetSums.forget K.2 S ⊆ T),
      ∏ p ∈ T, c p) =
      (∑ T ∈ spanningTrees K, ∏ p ∈ T, c p) * (codeTransferCurrent hK root c S).det := by
  have hp := congrArg (fun p : ℝ[X] => p.coeff (SubtypeSubsetSums.forget K.2 S).card)
    (code_tree_marker_identity hK root c hc S)
  rw [InclusionPolynomial.coeff_partition, Polynomial.coeff_C_mul] at hp
  have ht := InclusionPolynomial.coeff_det_one_add_X_top (codeTransferCurrent hK root c S)
  simp only [Fintype.card_coe, SubtypeSubsetSums.card_forget] at hp ht
  rwa [ht] at hp

theorem code_tree_inclusion_ratio (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) (hc : ∀ e : K.2, 0 < c e.val) (S : Finset K.2) :
    (∑ T ∈ (spanningTrees K).filter (fun T => SubtypeSubsetSums.forget K.2 S ⊆ T),
      ∏ p ∈ T, c p) / (∑ T ∈ spanningTrees K, ∏ p ∈ T, c p) =
      (codeTransferCurrent hK root c S).det := by
  have hZ : (∑ T ∈ spanningTrees K, ∏ p ∈ T, c p) ≠ 0 := by
    rw [← codeWeightedLaplacian_tree_partition hK root c]
    exact codeWeightedLaplacian_det_ne_zero hK root (fun e => c e.val) hc
  rw [code_tree_inclusion_mass hK root c hc S]
  exact mul_div_cancel_left₀ _ hZ

theorem codeTransferCurrent_one (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (S : Finset K.2) :
    codeTransferCurrent hK root (fun _ => 1) S =
      (Determinantal.transferKernel (codeIncidence hK root)).submatrix
        (Subtype.val : S → K.2) (Subtype.val : S → K.2) := by
  rw [← Determinantal.transferKernel_submatrix]
  simp [codeTransferCurrent, codeWeightedLaplacian, ReducedLaplacian.weightedLaplacian,
    codeIncidence, Matrix.mul_assoc]

theorem code_uniform_tree_inclusion_ratio
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1) (S : Finset K.2) :
    (((spanningTrees K).filter (fun T => SubtypeSubsetSums.forget K.2 S ⊆ T)).card : ℝ) /
      (spanningTrees K).card =
      ((Determinantal.transferKernel (codeIncidence hK root)).submatrix
        (Subtype.val : S → K.2) (Subtype.val : S → K.2)).det := by
  simpa only [Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    codeTransferCurrent_one] using
    code_tree_inclusion_ratio hK root (fun _ => 1) (fun _ => zero_lt_one) S

end Problem336

end

end OAI
