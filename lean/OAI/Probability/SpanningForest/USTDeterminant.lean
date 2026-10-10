import OAI.Probability.SpanningForest.CodedTransferBridge
import OAI.Probability.SpanningForest.USTInclusionCount
import OAI.Probability.SpanningForest.FiniteKernelSupport

namespace OAI

noncomputable section

open scoped BigOperators ENNReal
open Classical

namespace Problem336.FreeKernel

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem ustCylinder_positive_toReal_eq_det
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (A : Finset EdgeCode) (hA : ∀ e ∈ A, e.val ∈ K.2) :
    (ustCylinder K A ∅).toReal =
      Matrix.det (fun e f : A => inner ℝ (edgeVector e.val)
        (finiteKernel K (edgeVector f.val))) := by
  let S := USTInclusionCount.supportedPairs K A
  have hs : SubtypeSubsetSums.forget K.2 S = USTInclusionCount.edgePairs A :=
    USTInclusionCount.supportedPairs_map K A hA
  have hr := code_tree_inclusion_ratio hK root (fun _ => 1) (fun _ => zero_lt_one) S
  simp only [Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one, hs] at hr
  calc
    _ = (((spanningTrees K).filter
          (fun T => USTInclusionCount.edgePairs A ⊆ T)).card : ℝ) /
          (spanningTrees K).card := USTInclusionCount.ustCylinder_positive_toReal K A
    _ = (codeTransferCurrent hK root (fun _ => 1) S).det := hr
    _ = Matrix.det (fun e f : S =>
          inner ℝ (edgeVector ((CodedTransferBridge.edgeEquiv hK).symm e.val).val)
            (finiteKernel K (edgeVector ((CodedTransferBridge.edgeEquiv hK).symm f.val).val))) :=
      CodedTransferBridge.current_det_eq_finiteKernel hK root S
    _ = _ := by
      exact (Matrix.det_submatrix_equiv_self (USTInclusionCount.requiredEdgeEquiv K A hA)
        (fun e f : S =>
          inner ℝ (edgeVector ((CodedTransferBridge.edgeEquiv hK).symm e.val).val)
            (finiteKernel K (edgeVector ((CodedTransferBridge.edgeEquiv hK).symm f.val).val)))).symm

theorem ustCylinder_positive_eq_det_of_contained
    (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (A : Finset EdgeCode) (hA : ∀ e ∈ A, e.val ∈ K.2) :
    ustCylinder K A ∅ = ENNReal.ofReal
      (Matrix.det (fun e f : A => inner ℝ (edgeVector e.val)
        (finiteKernel K (edgeVector f.val)))) := by
  have hcard : (spanningTrees K).card ≠ 0 := by
    intro hz
    have hd := codeWeightedLaplacian_det_ne_zero hK root (fun _ => 1)
      (fun _ => zero_lt_one)
    apply hd
    rw [codeWeightedLaplacian_det_eq_tree_count]
    exact_mod_cast hz
  have hfinite : ustCylinder K A ∅ ≠ ∞ := by
    rw [USTInclusionCount.ustCylinder_positive_eq]
    exact ENNReal.div_ne_top (by simp) (by exact_mod_cast hcard)
  rw [← ENNReal.ofReal_toReal hfinite, ustCylinder_positive_toReal_eq_det hK root A hA]

theorem ustCylinder_positive_eq_finiteKernel_det
    (hK : IsFiniteConnectedSubgraph G K) (A : Finset EdgeCode) :
    ustCylinder K A ∅ = ENNReal.ofReal
      (Matrix.det (fun e f : A => inner ℝ (edgeVector e.val)
        (finiteKernel K (edgeVector f.val)))) := by
  let root : K.1 := ⟨hK.1.choose, hK.1.choose_spec⟩
  exact inclusion_identity_of_contained_identity K
    (ustCylinder_positive_eq_det_of_contained hK root) A

end Problem336.FreeKernel

end

end OAI
