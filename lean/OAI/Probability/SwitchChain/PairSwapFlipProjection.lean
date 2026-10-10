import OAI.Probability.SwitchChain.PairSwapFlip
import OAI.Probability.SwitchChain.SwitchFlip

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

theorem assignmentRelabel_swap_eq_flip
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm
      (assignmentRelabel G.val i j (Equiv.swap x y) T)).val =
    SwitchFlip.flip (fourVertexProposal i x.val y.val j h)
      ((stateFiberEquiv G i j hij).symm T).val :=
  assignmentRelabel_swap_eq_bidirectional G i j hij x y h T

theorem flip_leftSet_eq_map_swap
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j) :
    leftSet (SwitchFlip.flip (fourVertexProposal i x.val y.val j h) G).val i j =
      (leftSet G.val i j).map (Equiv.swap x.val y.val).toEmbedding := by
  let T : Assignment G.val i j :=
    ⟨leftSet G.val i j, leftSet_subset_singletonSet G.val i j, rfl⟩
  have hG : ((stateFiberEquiv G i j hij).symm T).val = G := by
    apply Subtype.ext
    exact trade_original G.val i j hij
  have he := assignmentRelabel_swap_eq_flip G i j hij x y h T
  rw [hG] at he
  rw [← he]
  exact (leftSet_trade G.val i j hij
    (assignmentRelabel G.val i j (Equiv.swap x y) T).val
    (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).trans
      (assignmentRelabel_swap_val G.val i j x y T)

theorem projection_at_assignment
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (f : PairResampling.StateSpace n d) (T : Assignment G.val i j) :
    SwitchFlip.projection (fourVertexProposal i x.val y.val j h) f
      ((stateFiberEquiv G i j hij).symm T).val =
    (f ((stateFiberEquiv G i j hij).symm T).val -
      f ((stateFiberEquiv G i j hij).symm
        (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) / 2 := by
  rw [SwitchFlip.projection_apply, assignmentRelabel_swap_eq_flip]

theorem sum_projection_sq_fiber_eq_assignment
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (f : PairResampling.StateSpace n d) :
    (∑ H ∈ PairResampling.fiberStates {i, j} G,
      (SwitchFlip.projection (fourVertexProposal i x.val y.val j h) f H) ^ 2) =
    (1 / 4 : ℝ) * ∑ T : Assignment G.val i j,
      (f ((stateFiberEquiv G i j hij).symm T).val -
        f ((stateFiberEquiv G i j hij).symm
          (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  rw [← Finset.sum_coe_sort]
  calc
    _ = ∑ T : Assignment G.val i j,
        (SwitchFlip.projection (fourVertexProposal i x.val y.val j h) f
          ((stateFiberEquiv G i j hij).symm T).val) ^ 2 := by
      exact ((resamplingFiberEquiv G i j hij).symm.sum_comp
        (fun H => (SwitchFlip.projection (fourVertexProposal i x.val y.val j h) f H.val) ^ 2)).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [projection_at_assignment]
      ring

theorem projection_eq_zero_of_not_singleton
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hout : ¬ (u ∈ singletonSet G.val i j ∧ v ∈ singletonSet G.val i j))
    (f : PairResampling.StateSpace n d) :
    SwitchFlip.projection (fourVertexProposal i u v j h) f G = 0 := by
  rw [SwitchFlip.projection_apply]
  have hf : SwitchFlip.flip (fourVertexProposal i u v j h) G = G :=
    bidirectional_eq_self_of_not_singleton G i u v j h hout
  rw [hf]
  ring

end Problem315.PairFiber

end

end OAI
