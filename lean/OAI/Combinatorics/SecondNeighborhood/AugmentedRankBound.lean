import OAI.Combinatorics.SecondNeighborhood.AugmentedMatching
import OAI.Combinatorics.SecondNeighborhood.RankBoundFromMinors

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem augmented_matching_card_le_corners
    (r : X → X → Prop) (R C : Finset (X × X))
    (M : Finset (LeftVertex r R C × RightVertex r R C))
    (hM : IsMatching (AugmentedEdge r R C) M)
    (hα : IsMaximumMatching (AlphaRelation r R C) (alphaEdges M))
    (hβ : IsMaximumMatching (BetaRelation r R C) (betaEdges M)) :
    M.card ≤ (Z r R C).card + (H r R C).card := by
  classical
  have hαrelation : matrixLSupport r R C = AlphaRelation r R C := by
    funext z a
    exact propext (matrixLSupport_iff_leftCovers r R C z a)
  have hβrelation : matrixNTransposeSupport r R C = BetaRelation r R C := by
    funext z b
    exact propext (matrixNTransposeSupport_iff_rightCovers r R C z b)
  have hα' : IsMaximumMatching (matrixLSupport r R C) (alphaEdges M) := by
    rw [hαrelation]
    exact hα
  have hβ' : IsMaximumMatching (matrixNTransposeSupport r R C) (betaEdges M) := by
    rw [hβrelation]
    exact hβ
  have hOriginal := originalEdges_isMatching hM
  have hleft : Function.Injective (fun e : ↥(originalEdges M) => e.val.1) := by
    intro e f hef
    apply Subtype.ext
    exact hOriginal.2.1 e.property f.property hef
  have hright : Function.Injective (fun e : ↥(originalEdges M) => e.val.2) := by
    intro e f hef
    apply Subtype.ext
    exact hOriginal.2.2 e.property f.property hef
  have hbound := original_add_auxiliary_card_le_corners
    r R C (alphaEdges M) (betaEdges M) hα' hβ'
    (fun e : ↥(originalEdges M) => e.val.1)
    (fun e : ↥(originalEdges M) => e.val.2) hleft hright
    (fun e f => original_alpha_left_ne hM e.property f.property)
    (fun e f => original_beta_right_ne hM e.property f.property)
    (fun e => hOriginal.1 e.val e.property)
  rw [augmented_matching_card hM]
  simpa only [Fintype.card_coe] using hbound

end SeymourSecondNeighborhood.Pruning

end OAI
