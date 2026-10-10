import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.PathVisitProbability
import OAI.Combinatorics.TriangleRemoval.Queries.JointMarkedQueryPair

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section TracePairProbability
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def actualPairVisitProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ)
    (path₁ path₂ : List (ι × τ)) : ℝ :=
  (((ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map
      (fun z => z.2.any (fun c => decide (c.address = path₁.reverse)) &&
        z.2.any (fun c => decide (c.address = path₂.reverse)))) true).toReal

theorem actualPairVisitProbability_le_marked (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (path₁ path₂ : List (ι × τ)) :
    actualPairVisitProbability H N d k focus parent path₁ path₂ ≤
      pairVisitProbability H N d k focus parent path₁ path₂ := by
  let c : QueryCall ι τ := ⟨[],focus,parent⟩
  let ν := fun _ : τ => PMF.uniformOfFintype (Fin N)
  let P := ExposureTree.fresh ν (jointMarkedQuery H N (pairRequired path₁ path₂) d k c)
  have ht : P.map (fun z => (z.1,z.2.2)) =
      ExposureTree.fresh ν (tracedGridQuery H N d k c) := by
    rw [← ExposureTree.fresh_mapOutput,jointMarkedQuery_trace]
  have hm : P.map (fun z => (z.1,z.2.1)) =
      ExposureTree.fresh ν (markedGridQueryDepth H N (pairRequired path₁ path₂) d k [] focus parent) := by
    rw [← ExposureTree.fresh_mapOutput,jointMarkedQuery_marked]
  unfold actualPairVisitProbability pairVisitProbability
  rw [markedGood_map_true,← ht,← hm,PMF.map_comp,PMF.map_comp]
  apply pmf_boolean_map_le
  intro z hz hh
  obtain ⟨hp,hq⟩ := Bool.and_eq_true_iff.mp hh
  obtain ⟨a,ha,hea⟩ := List.any_eq_true.mp hp
  obtain ⟨b,hb,heb⟩ := List.any_eq_true.mp hq
  apply jointMarkedQuery_pair_hit H N d k c path₁ path₂ ν hz
  · exact ⟨a,ha,by simpa only [c,List.append_nil] using of_decide_eq_true hea⟩
  · exact ⟨b,hb,by simpa only [c,List.append_nil] using of_decide_eq_true heb⟩

end TracePairProbability
end SharpTerminalLeave

end

end OAI
