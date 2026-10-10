import OAI.Probability.SpanningForest.USTInclusionCount
import OAI.Probability.SpanningForest.CodedTransferProjection
import OAI.Probability.SpanningForest.FiniteKernelSupport

namespace OAI

noncomputable section

open scoped ENNReal

namespace Problem336.FreeKernel

open USTInclusionCount

variable {G : GraphCode} {K : FiniteSubgraphCode}

theorem ustCylinder_toReal_eq_finiteKernel_minor_of_contained
    (hK : IsFiniteConnectedSubgraph G K) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) :
    (ustCylinder K A ∅).toReal =
      Matrix.det (fun e f : A => inner ℝ (edgeVector e.val)
        (finiteKernel K (edgeVector f.val))) := by
  classical
  let root : K.1 := ⟨hK.1.choose, hK.1.choose_spec⟩
  have hf : SubtypeSubsetSums.forget K.2 (supportedPairs K A) = edgePairs A :=
    supportedPairs_map K A hA
  rw [ustCylinder_positive_toReal]
  have hc := CodeTransferKernel.code_tree_inclusion_ratio_finiteKernel hK root
    (supportedPairs K A)
  rw [hf] at hc
  rw [hc]
  exact (det_required_reindex K A hA
    (fun e f : K.2 => inner ℝ (edgeVector (CodeTransferKernel.edgeEquiv hK e).val)
      (finiteKernel K (edgeVector (CodeTransferKernel.edgeEquiv hK f).val)))).symm

theorem spanningTrees_card_ne_zero (hK : IsFiniteConnectedSubgraph G K) :
    (spanningTrees K).card ≠ 0 := by
  let root : K.1 := ⟨hK.1.choose, hK.1.choose_spec⟩
  have hd := codeWeightedLaplacian_det_ne_zero hK root (fun _ => 1)
    (fun _ => by norm_num)
  rw [codeWeightedLaplacian_det_eq_tree_count] at hd
  exact_mod_cast hd

theorem ustCylinder_eq_finiteKernel_minor_of_contained
    (hK : IsFiniteConnectedSubgraph G K) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) :
    ustCylinder K A ∅ = ENNReal.ofReal
      (Matrix.det (fun e f : A => inner ℝ (edgeVector e.val)
        (finiteKernel K (edgeVector f.val)))) := by
  rw [← ustCylinder_toReal_eq_finiteKernel_minor_of_contained hK A hA]
  apply (ENNReal.ofReal_toReal ?_).symm
  unfold ustCylinder
  apply ENNReal.div_ne_top
  · exact ENNReal.natCast_ne_top _
  · exact_mod_cast spanningTrees_card_ne_zero hK

theorem ustCylinder_eq_finiteKernel_minor
    (hK : IsFiniteConnectedSubgraph G K) (A : Finset EdgeCode) :
    ustCylinder K A ∅ = ENNReal.ofReal
      (Matrix.det (fun e f : A => inner ℝ (edgeVector e.val)
        (finiteKernel K (edgeVector f.val)))) :=
  inclusion_identity_of_contained_identity K
    (ustCylinder_eq_finiteKernel_minor_of_contained hK) A

end Problem336.FreeKernel

end

end OAI
