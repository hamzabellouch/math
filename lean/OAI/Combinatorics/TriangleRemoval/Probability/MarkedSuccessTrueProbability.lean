import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.FinsetCandidateOrder

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma markedSuccess_eq_trueProbability_fst (p : PMF (Bool × Bool)) :
    markedSuccess p = trueProbability (p.map Prod.fst) := by
  have hp := pmfMean_map p Prod.fst (fun b : Bool => if b then (1:ℝ) else 0)
  rw [← markedSuccess] at hp
  rw [← hp]
  simp [pmfMean,trueProbability]

section CandidateMarginal
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem markedChildKernel_success (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (u : Fin N) :
    markedSuccess (markedChildKernel H N required d address focus parent a u) =
      gridAnswerProbability H N d u.val ((H a.val.2).erase a.val.1) (some a.val.2) := by
  rw [markedSuccess_eq_trueProbability_fst]
  unfold markedChildKernel
  rw [← ExposureTree.fresh_mapOutput,markedGridQueryDepth_outcome]
  rfl

theorem markedChildKernel_success_complete (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (u : Fin N) (hu : u.val ≤ d) :
    markedSuccess (markedChildKernel H N required d address focus parent a u) =
      ∏ f ∈ (H a.val.2).erase a.val.1, gridMessage H N N u.val f (some a.val.2) := by
  rw [markedChildKernel_success,gridAnswerProbability_factor]
  apply Finset.prod_congr rfl
  intro f _
  exact gridMessage_stable H N u.val d N hu u.isLt.le f (some a.val.2)

end CandidateMarginal
end SharpTerminalLeave

end

end OAI
