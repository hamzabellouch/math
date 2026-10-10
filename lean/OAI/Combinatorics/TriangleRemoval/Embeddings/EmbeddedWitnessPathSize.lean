import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.LegalCollisionPairs
import OAI.Combinatorics.TriangleRemoval.Process.WitnessDimensions
import OAI.Combinatorics.TriangleRemoval.Queries.AddressHead
import OAI.Combinatorics.TriangleRemoval.Process.IndexedAttachmentOlder
import OAI.Combinatorics.TriangleRemoval.Process.ThreeChooseBound

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma embeddedWitness_path_size {n R d : ℕ} {G : Graph n}
    (W : BoundedEmbeddedWitness G R d) :
    let p := (embeddedWitnessPaths W).1
    let q := (embeddedWitnessPaths W).2
    (splitQueryPaths p q).1.length + (splitQueryPaths p q).2.1.length +
      (splitQueryPaths p q).2.2.length = W.1.val.2.val := by
  let q := W.1
  let w := W.2.2.1
  let ψ := W.2.2.2.val
  let key := indexedTriangleKey (dimensionBirth q) w.2.2.val ψ
  have hk : Function.Injective key := indexed_triangle_key_injective (fun _ => rfl)
    W.2.1.property w.2.1.val w.2.2.val w.2.2.property ψ
  exact w.2.1.val.two_mark_exact_size hk _ _ w.2.1.property

lemma embeddedWitness_factorial_weight {n R d : ℕ} {G : Graph n}
    (W : BoundedEmbeddedWitness G R d) {x : ℝ} (hx : 0 ≤ x) :
    pairFactorialWeight x (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2 ≤
      (3*x)^W.1.val.2.val / (W.1.val.2.val.factorial : ℝ) := by
  unfold pairFactorialWeight
  have hh := total_three_segment_weight_le hx
    (splitQueryPaths (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2).1.length
    (splitQueryPaths (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2).2.1.length
    (splitQueryPaths (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2).2.2.length
  dsimp only
  rw [embeddedWitness_path_size W] at hh ⊢
  exact hh

section AnyPaths
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma actualPairVisitProbability_zero_of_illegal (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ))
    (hbad : ¬ (p ∈ legalPaths H d focus parent ∧ q ∈ legalPaths H d focus parent)) :
    actualPairVisitProbability H N d k focus parent p q = 0 := by
  classical
  rw [← log_pair_probability]
  let P := ExposureTree.freshLog (gridPriorities N) (tracedGridQuery H N d k ⟨[],focus,parent⟩)
  let ev := fun (z : (Bool × List (QueryCall ι τ)) × List τ) =>
    z.1.2.any (fun c => decide (c.address = p.reverse)) &&
      z.1.2.any (fun c => decide (c.address = q.reverse))
  have hnone : ∀ z ∈ P.support, ev z = false := by
    intro z hz
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨hp,hq⟩ := Bool.and_eq_true_iff.mp he
    have hlegal (path : List (ι × τ)) (h : z.1.2.any (fun c => decide (c.address = path.reverse)) = true) :
        path ∈ legalPaths H d focus parent := by
      obtain ⟨a,ha,heq⟩ := List.any_eq_true.mp h
      have haeq : a.address = path.reverse := of_decide_eq_true heq
      obtain ⟨path',hp',ha'⟩ := tracedGridQuery_legal_path H N d k ⟨[],focus,parent⟩
        (gridPriorities N) hz a ha
      rw [ha',callAtPath_address,List.append_nil] at haeq
      have hh : path' = path := List.reverse_injective haeq
      exact hh ▸ hp'
    exact hbad ⟨hlegal p hp,hlegal q hq⟩
  have heq := pmf_map_congr_support P ev (fun _ => false) hnone
  change ((P.map ev) true).toReal = 0
  rw [heq]
  change ((P.map (Function.const _ false)) true).toReal = 0
  rw [PMF.map_const]
  simp

theorem actualPairVisitProbability_weight_any (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N) (focus : Finset ι) (parent : Option τ)
    (p q : List (ι × τ)) :
    actualPairVisitProbability H N d k focus parent p q ≤
      C^3 * pairFactorialWeight (prefixWeight (fun t => (2/(N : ℝ))*b t) k) p q := by
  by_cases h : p ∈ legalPaths H d focus parent ∧ q ∈ legalPaths H d focus parent
  · exact actualPairVisitProbability_weight H N b hb hq C hC hlower d k hkd hkN focus parent p q h.1 h.2
  · rw [actualPairVisitProbability_zero_of_illegal H N d k focus parent p q h]
    apply mul_nonneg (pow_nonneg (by linarith) _)
    apply pairFactorialWeight_nonneg
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (by positivity) (hb t)

end AnyPaths
end SharpTerminalLeave

end

end OAI
