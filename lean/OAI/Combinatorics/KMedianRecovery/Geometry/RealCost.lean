import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.SampledSurrogate
import OAI.Combinatorics.KMedianRecovery.Branching.SurrogateRealization

namespace OAI

namespace MetricKMedianRecovery.Completion
open Categorical FiniteSampling
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def realCost (D U : Finset V) : ℝ :=
  if h : U.Nonempty then ∑ p ∈ D, distanceTo U h p else 0

lemma sampled_metric_branch {E R B : Type*} [Fintype E] [DecidableEq E]
    [Fintype R] [Fintype B] [DecidableEq R] {a c q : ℕ}
    (D F S Q G : Finset V) (hS : S ⊆ F) (hn : S.Nonempty) (hQ : Q ⊆ S)
    (part : E → Fin a) (hp : Function.Surjective part) (loc : E → V)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (hr : ∀ i, 0 ≤ radius i) (hM0 : 0 ≤ M)
    (hloc : ∀ e, loc e ∈ F) (hball : ∀ e, dist (w (part e)) (loc e) ≤ radius (part e))
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M)
    (redLoc : R → V) (blueLoc blueDest : B → V)
    (hredInj : Function.Injective redLoc) (hblueInj : Function.Injective blueLoc)
    (hred : ∀ r, redLoc r ∈ S \ Q) (hblue : ∀ b, blueLoc b ∈ S \ Q)
    (hRB : ∀ r b, redLoc r ≠ blueLoc b)
    (hG : G ⊆ S \ Q) (hGR : ∀ r, redLoc r ∉ G) (hGB : ∀ b, blueLoc b ∉ G)
    (hdest : ∀ b, blueDest b ∈ F) (hdestCount : (Finset.univ.image blueDest).card ≤ c)
    (hq : q ≤ Fintype.card R) (hcount : a+c ≤ Q.card+q+Fintype.card B)
    (K : ℝ)
    (hK : (∑ b, assignmentWeight D (nearestTag (S \ Q) w radius M) (blueLoc b) *
      dist (blueLoc b) (blueDest b)) ≤ K)
    (theta : ℝ) (htheta : 1/Real.exp 1 < theta) :
    let Ψ := surrogate (P := ↥D) K q
      (fun p => virtualNearest (S \ Q) w radius M p)
      (fun p e => dist (p : V) (loc e))
      (fun r => assignmentWeight D (nearestTag (S \ Q) w radius M) (redLoc r))
      (fun r => virtualNearest G w radius M (redLoc r))
      (fun r e => dist (redLoc r) (loc e))
    ∃ out : (BinaryOracleIndex E a (stepExponent a (theta-1/Real.exp 1))
        (sampleCount (Fintype.card E) a (theta-1/Real.exp 1)) → Bool) → Finset V,
      (∀ bits, out bits ⊆ F ∧ (out bits).card = S.card ∧ (out bits).Nonempty) ∧
      ∀ X, PartitionFeasible part X →
        average (fun bits => realCost D (out bits)) ≤ theta * Ψ ∅ + (1-theta) * Ψ X := by
  classical
  dsimp only
  let base : ↥D → ℝ := fun p => virtualNearest (S \ Q) w radius M p
  let distance : ↥D → E → ℝ := fun p e => dist (p : V) (loc e)
  let weight : R → ℝ := fun r => assignmentWeight D (nearestTag (S \ Q) w radius M) (redLoc r)
  let redBase : R → ℝ := fun r => virtualNearest G w radius M (redLoc r)
  let redDistance : R → E → ℝ := fun r e => dist (redLoc r) (loc e)
  let choice := sampledSurrogate part hp K q base distance weight redBase redDistance
    (theta-1/Real.exp 1)
  have hreal : ∀ bits, ∃ U : Finset V, U ⊆ F ∧ U.card = S.card ∧ U.Nonempty ∧
      realCost D U ≤ surrogate K q base distance weight redBase redDistance (choice bits) := by
    intro bits
    obtain ⟨U, hUF, hUc, hUn, hcost⟩ := surrogate_realization
      D F S Q G hS hn hQ part hp loc w radius M hr hM0 hloc hball hM
      redLoc blueLoc blueDest hredInj hblueInj hred hblue hRB hG hGR hGB hdest hdestCount
      hq hcount K hK (choice bits) (sampledSurrogate_feasible part hp K q base distance
        weight redBase redDistance (theta-1/Real.exp 1) bits)
    refine ⟨U, hUF, hUc, hUn, ?_⟩
    simp only [realCost, dite_eq_left hUn]
    change (∑ p ∈ D, distanceTo U hUn p) ≤
      K + (∑ p : ↥D, cappedCost (virtualNearest (S \ Q) w radius M p)
        (fun e => dist (p : V) (loc e)) (choice bits)) + _
    rw [Finset.sum_coe_sort D (fun p => cappedCost (virtualNearest (S \ Q) w radius M p)
      (fun e => dist p (loc e)) (choice bits))]
    exact hcost
  choose out hout using hreal
  refine ⟨out, fun bits => ⟨(hout bits).1, (hout bits).2.1, (hout bits).2.2.1⟩, ?_⟩
  intro X hX
  refine (average_mono (fun bits => (hout bits).2.2.2)).trans ?_
  exact sampledSurrogate_expected part hp K q base distance weight redBase redDistance
    (fun r => assignmentWeight_nonneg _ _ _) htheta X hX

end MetricKMedianRecovery.Completion

end OAI
