import OAI.Probability.SwitchChain.PairSwapInactive
import OAI.Probability.SwitchChain.SwitchFlip

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.SwitchFlip

theorem flip_fourVertex_of_nonsingleton
    {n : ℕ} {d : Fin n → ℕ} (G : GraphState n d) (i k l j : Fin n)
    (h : FourDistinct i k l j)
    (hinactive : k ∉ PairFiber.singletonSet G.val i j ∨
      l ∉ PairFiber.singletonSet G.val i j) :
    flip (fourVertexProposal i k l j h) G = G :=
  PairFiber.bidirectional_proposal_fix_of_nonsingleton G i k l j h hinactive

theorem projection_fourVertex_apply_of_nonsingleton
    {n : ℕ} {d : Fin n → ℕ} (f : PairResampling.StateSpace n d)
    (G : GraphState n d) (i k l j : Fin n) (h : FourDistinct i k l j)
    (hinactive : k ∉ PairFiber.singletonSet G.val i j ∨
      l ∉ PairFiber.singletonSet G.val i j) :
    projection (fourVertexProposal i k l j h) f G = 0 := by
  rw [projection_apply, flip_fourVertex_of_nonsingleton G i k l j h hinactive]
  simp

theorem projection_fourVertex_apply_on_inactive_fiber
    {n : ℕ} {d : Fin n → ℕ} (f : PairResampling.StateSpace n d)
    (G H : GraphState n d) (i k l j : Fin n) (h : FourDistinct i k l j)
    (hH : H ∈ PairResampling.fiberStates {i, j} G)
    (hinactive : k ∉ PairFiber.singletonSet G.val i j ∨
      l ∉ PairFiber.singletonSet G.val i j) :
    projection (fourVertexProposal i k l j h) f H = 0 := by
  apply projection_fourVertex_apply_of_nonsingleton f H i k l j h
  exact PairFiber.nonsingleton_of_sameFiber i j k l h.2.2.1
    ((PairResampling.mem_fiberStates {i, j} G H).mp hH) hinactive

theorem sum_projection_sq_on_inactive_fiber
    {n : ℕ} {d : Fin n → ℕ} (f : PairResampling.StateSpace n d)
    (G : GraphState n d) (i k l j : Fin n) (h : FourDistinct i k l j)
    (hinactive : k ∉ PairFiber.singletonSet G.val i j ∨
      l ∉ PairFiber.singletonSet G.val i j) :
    (∑ H ∈ PairResampling.fiberStates {i, j} G,
      (projection (fourVertexProposal i k l j h) f H) ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intro H hH
  rw [projection_fourVertex_apply_on_inactive_fiber f G H i k l j h hH hinactive]
  norm_num

end Problem315.SwitchFlip

end

end OAI
