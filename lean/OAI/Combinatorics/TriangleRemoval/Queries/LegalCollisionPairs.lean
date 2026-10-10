import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.GridCollision
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraphLinear
import OAI.Combinatorics.TriangleRemoval.Queries.SplitQueryPaths

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
section CollisionPathSum
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def legalCollisionPairs (H : τ → Finset ι) (d : ℕ)
    (focus : Finset ι) (parent : Option τ) : Finset (List (ι × τ) × List (ι × τ)) := by
  classical
  let c : QueryCall ι τ := ⟨[],focus,parent⟩
  exact ((legalPaths H d focus parent).product (legalPaths H d focus parent)).filter
    (fun pq => pq.1 ≠ pq.2 ∧ ∃ T, T ∈ (callAtPath H c pq.1).keys H ∧
      T ∈ (callAtPath H c pq.2).keys H)

noncomputable def tracedCollisionProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) : ℝ :=
  (((ExposureTree.freshLog (gridPriorities N)
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map
      (fun z => ExposureTree.repeats ∅ z.2)) true).toReal

lemma gridCollision_eq_trace (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) (j : ℕ) :
    gridCollision H focus parent j = tracedCollisionProbability H (j+1) (j+1) (j+1) focus parent := by
  unfold gridCollision trueProbability tracedCollisionProbability
  rw [ExposureTree.freshRecorded_eq_log,PMF.map_comp]
  rw [← tracedGridQuery_outcome H (j+1) (j+1) (j+1) ⟨[],focus,parent⟩,
    ExposureTree.freshLog_mapOutput,PMF.map_comp]
  rfl

lemma log_pair_probability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ)) :
    (((ExposureTree.freshLog (gridPriorities N)
      (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map (fun z =>
        z.1.2.any (fun c => decide (c.address = p.reverse)) &&
        z.1.2.any (fun c => decide (c.address = q.reverse)))) true).toReal =
      actualPairVisitProbability H N d k focus parent p q := by
  unfold actualPairVisitProbability
  change _ = (((ExposureTree.fresh (gridPriorities N)
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map _) true).toReal
  rw [← ExposureTree.freshLog_outcome,PMF.map_comp]
  rfl

end CollisionPathSum

theorem graph_collision_path_sum {n : ℕ} (G focus : Graph n) (parent : Option (Finset (Fin n)))
    (hc : (QueryCall.mk [] focus parent).Separated (triangleHypergraph G))
    (N : ℕ) [NeZero N] (d k : ℕ) :
    tracedCollisionProbability (triangleHypergraph G) N d k focus parent ≤
      ∑ pq ∈ legalCollisionPairs (triangleHypergraph G) d focus parent,
        actualPairVisitProbability (triangleHypergraph G) N d k focus parent pq.1 pq.2 := by
  classical
  let H := triangleHypergraph G
  let c : QueryCall (Finset (Fin n)) (Finset (Fin n)) := ⟨[],focus,parent⟩
  let P := ExposureTree.freshLog (gridPriorities N) (tracedGridQuery H N d k c)
  let ev := fun (pq : List (Finset (Fin n) × Finset (Fin n)) ×
      List (Finset (Fin n) × Finset (Fin n)))
      (z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n))) =>
    z.1.2.any (fun a : QueryCall (Finset (Fin n)) (Finset (Fin n)) => decide (a.address = pq.1.reverse)) &&
    z.1.2.any (fun a : QueryCall (Finset (Fin n)) (Finset (Fin n)) => decide (a.address = pq.2.reverse))
  have hcov : ∀ z ∈ P.support, ExposureTree.repeats ∅ z.2 = true →
      ∃ pq ∈ legalCollisionPairs H d focus parent, ev pq z = true := by
    intro z hz hr
    obtain ⟨a,ha,b,hb,hab,T,haT,hbT⟩ := graph_query_repeat_addresses G N d k c hc
      (gridPriorities N) hz hr
    obtain ⟨p,hp,rfl⟩ := tracedGridQuery_legal_path H N d k c (gridPriorities N) hz a ha
    obtain ⟨q,hq,rfl⟩ := tracedGridQuery_legal_path H N d k c (gridPriorities N) hz b hb
    have hpq : p ≠ q := by intro he; subst q; exact hab rfl
    refine ⟨(p,q),?_,Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hp,hq⟩,hpq,T,haT,hbT⟩
    · apply List.any_eq_true.mpr
      refine ⟨callAtPath H c p,ha,?_⟩
      simp only [callAtPath_address,c,List.append_nil,decide_true]
    · apply List.any_eq_true.mpr
      refine ⟨callAtPath H c q,hb,?_⟩
      simp only [callAtPath_address,c,List.append_nil,decide_true]
  have hh := pmf_boolean_finite_cover P (legalCollisionPairs H d focus parent)
    (fun z => ExposureTree.repeats ∅ z.2) ev hcov
  change tracedCollisionProbability H N d k focus parent ≤ _
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro pq _
  exact log_pair_probability H N d k focus parent pq.1 pq.2

theorem graph_collision_weighted_path_sum {n : ℕ} (G focus : Graph n)
    (parent : Option (Finset (Fin n)))
    (hc : (QueryCall.mk [] focus parent).Separated (triangleHypergraph G))
    (N : ℕ) [NeZero N] (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t)
    (hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N) :
    tracedCollisionProbability (triangleHypergraph G) N d k focus parent ≤
      C^3 * ∑ pq ∈ legalCollisionPairs (triangleHypergraph G) d focus parent,
        pairFactorialWeight (prefixWeight (fun t => (2/(N : ℝ))*b t) k) pq.1 pq.2 := by
  apply (graph_collision_path_sum G focus parent hc N d k).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro pq hpq
  obtain ⟨hp,hq'⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpq).1
  exact actualPairVisitProbability_weight (triangleHypergraph G) N b hb hq C hC hlower
    d k hkd hkN focus parent pq.1 pq.2 hp hq'

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
