import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedCountedTracedRepeat
import OAI.Combinatorics.TriangleRemoval.Embeddings.EmbeddedWitnessPathSize

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

theorem canonical_collision_sum (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (focus : Graph n) (parent : Option (Finset (Fin n)))
    (_hM : EdgeMatching focus) (_hG : focus ⊆ G) (_hr : focus.card ≤ 2)
    (_hc : (QueryCall.mk [] focus parent).Separated (triangleHypergraph G))
    (N : ℕ) [NeZero N] (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t)
    (_hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
    tracedCollisionProbability (triangleHypergraph G) N d k focus parent ≤
      ∑ W : BoundedEmbeddedWitness G (focus.biUnion id).card d,
        if WitnessEmbeddingBound focus.card W ∧ embeddedWitnessRoots W = focus then
          C^3 * ((3*prefixWeight (fun t => (2/(N : ℝ))*b t) k)^W.1.val.2.val /
            (W.1.val.2.val.factorial : ℝ)) else 0 := by
  classical
  filter_upwards [rooted_counted_traced_repeat_cover c₀ C₀ hc₀] with n hn
  intro G hGood focus parent hM hG hr hc N _ b hb hq C hC hlower d k hkd hkN
  let H := triangleHypergraph G
  let P := ExposureTree.freshLog (gridPriorities N)
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)
  let S : Finset (BoundedEmbeddedWitness G (focus.biUnion id).card d) :=
    Finset.univ.filter (fun W => WitnessEmbeddingBound focus.card W ∧ embeddedWitnessRoots W = focus)
  let ev := fun (W : BoundedEmbeddedWitness G (focus.biUnion id).card d)
      (z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n))) =>
    z.1.2.any (fun a => decide (a.address = (embeddedWitnessPaths W).1.reverse)) &&
      z.1.2.any (fun a => decide (a.address = (embeddedWitnessPaths W).2.reverse))
  have hcov : ∀ z ∈ P.support, ExposureTree.repeats ∅ z.2 = true →
      ∃ W ∈ S, ev W z = true := by
    intro z hz hzrep
    obtain ⟨W,hW,hroots,⟨a,ha,hae⟩,⟨b,hb',hbe⟩⟩ :=
      hn G hGood focus parent hM hG hr hc N d k (gridPriorities N) z hz hzrep
    refine ⟨W,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hW,hroots⟩,?_⟩
    apply Bool.and_eq_true_iff.mpr
    exact ⟨List.any_eq_true.mpr ⟨a,ha,decide_eq_true hae⟩,
      List.any_eq_true.mpr ⟨b,hb',decide_eq_true hbe⟩⟩
  have hh := pmf_boolean_finite_cover P S (fun z => ExposureTree.repeats ∅ z.2) ev hcov
  change tracedCollisionProbability H N d k focus parent ≤ _ at hh
  apply hh.trans
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum
  intro W _
  change (((ExposureTree.freshLog (gridPriorities N)
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map (fun z =>
      z.1.2.any (fun a => decide (a.address = (embeddedWitnessPaths W).1.reverse)) &&
      z.1.2.any (fun a => decide (a.address = (embeddedWitnessPaths W).2.reverse)))) true).toReal ≤ _
  rw [log_pair_probability]
  apply (actualPairVisitProbability_weight_any H N b hb hq C hC hlower
    d k hkd hkN focus parent (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
  apply embeddedWitness_factorial_weight W
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (by positivity) (hb t)

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable instance canonicalCollisionSumIndexedWitnessCodeFintype
    {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Fintype (IndexedWitnessCode E birth mark) := by
  classical
  unfold IndexedWitnessCode
  infer_instance

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
