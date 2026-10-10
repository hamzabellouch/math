import OAI.Geometry.RCD.Transport.RenyiScalarMidpoint
import OAI.Geometry.RCD.Transport.ReducedChord

namespace OAI

/-! # The finite-dimensional scalar chord along the fixed dyadic tree

This is Rajala's preliminary estimate (3.1), retaining the dimension in
the exact reduced coefficient. It will provide endpoint entropy continuity.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem FollowsRenyiTree.reducedChord
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N)
    (S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K (1-1/N) a) (m : ℕ) :
    ∀ {a : RenyiTransportNode n X} {ν : Time → Measure X}, FollowsRenyiTree S a ν m →
      ∀ t∈dyadicGrid m,
      reducedChord K (N+1) a.distance (renyiIntegral (hausdorff n X) a.left N)
        (renyiIntegral (hausdorff n X) a.right N) t ≤ renyiIntegral (hausdorff n X) (ν t) N := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hNp : 1<N+1 := by linarith
  induction m with
  | zero =>
    intro a ν h t ht
    rcases ht with rfl | ht
    · rw [reducedChord_zero hK hNp a.distance_nonneg,h.1]
    · have he : t=1 := ht
      subst t
      rw [reducedChord_one hK hNp a.distance_nonneg,h.2]
  | succ m ih =>
    intro a ν h t ht
    have hm := hX.renyiNode_scalar_midpoint K n hn hK hN a (S a)
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [reducedChord_lower hK hNp a.distance_nonneg]
      refine (reducedChord_mono le_rfl hm s).trans ?_
      have hi := ih h.2.2.2.1 s hs
      simpa only [RenyiNodeSplit.leftNode_distance,RenyiNodeSplit.leftNode_left,
        RenyiNodeSplit.leftNode_right] using hi
    · rw [reducedChord_upper hK hNp a.distance_nonneg]
      refine (reducedChord_mono hm le_rfl s).trans ?_
      have hi := ih h.2.2.2.2 s hs
      simpa only [RenyiNodeSplit.rightNode_distance,RenyiNodeSplit.rightNode_left,
        RenyiNodeSplit.rightNode_right] using hi

end RegularPointCoordinates

end

end OAI
