import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.CardBiUnion
import OAI.Combinatorics.TriangleRemoval.Probability.UniformSingletonRootSet

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem canonical_collision_singleton_sum (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (e : Finset (Fin n)), e ∈ G →
    ∀ (N : ℕ) [NeZero N] (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t)
    (_hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
    tracedCollisionProbability (triangleHypergraph G) N d k {e} none ≤
      ∑ W : BoundedEmbeddedWitness G 2 d,
        if WitnessEmbeddingBound 1 W ∧ embeddedWitnessRoots W = {e} then
          C^3 * ((3*prefixWeight (fun t => (2/(N : ℝ))*b t) k)^W.1.val.2.val /
            (W.1.val.2.val.factorial : ℝ)) else 0 := by
  classical
  filter_upwards [canonical_collision_sum c₀ C₀ hc₀] with n hn
  intro G hGood e he N _ b hb hq C hC hlower d k hkd hkN
  have he2 := mem_completeGraph.mp (hGood.1 he)
  have hh := hn G hGood {e} none (EdgeMatching.singleton e he2)
    (Finset.singleton_subset_iff.mpr he) (by simp) (separated_singleton _ [] e none)
    N b hb hq C hC hlower d k hkd hkN
  have hbi : (({e} : Graph n).biUnion id).card = 2 := by simpa only [Finset.singleton_biUnion,id_eq] using he2
  rw [hbi] at hh
  simpa only [Finset.card_singleton] using hh

theorem averaged_singleton_grid_collision (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (hne : G.Nonempty) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t) (_hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        tracedCollisionProbability (triangleHypergraph G) N d k {e} none) ≤
      (8192*C^3/prefixD n^50)*
        Real.exp (45*prefixD n*prefixWeight (fun t => (2/(N : ℝ))*b t) k) := by
  classical
  filter_upwards [canonical_collision_singleton_sum c₀ C₀ hc₀] with n hn
  intro G hGood hne N _ b hb hq C hC hlower d k hkd hkN
  let x := prefixWeight (fun t => (2/(N : ℝ))*b t) k
  have hx : 0 ≤ x := by
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (by positivity) (hb t)
  let w (W : BoundedEmbeddedWitness G 2 d) : ℝ :=
    if WitnessEmbeddingBound 1 W then C^3*((3*x)^W.1.val.2.val/(W.1.val.2.val.factorial : ℝ)) else 0
  have hw (W : BoundedEmbeddedWitness G 2 d) : 0 ≤ w W := by
    dsimp only [w]
    split_ifs <;> positivity
  have hcover : pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        tracedCollisionProbability (triangleHypergraph G) N d k {e} none) ≤
      pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        ∑ W : BoundedEmbeddedWitness G 2 d,
          if embeddedWitnessRoots W = {e} then w W else 0) := by
    apply pmfMean_mono
    intro e he
    have heG := (PMF.mem_support_uniformOfFinset_iff hne e).mp he
    have hh := hn G hGood e heG N b hb hq C hC hlower d k hkd hkN
    apply hh.trans_eq
    apply Finset.sum_congr rfl
    intro W _
    by_cases hW : WitnessEmbeddingBound 1 W <;>
      by_cases hroot : embeddedWitnessRoots W = {e} <;>
        simp [w,x,hW,hroot]
  have hsample := uniform_singleton_root_weighted_sum G hne embeddedWitnessRoots w hw
  have hm : 0 ≤ prefixM n := by rw [← hGood.2.1]; positivity
  have hmpos : 0 < prefixM n := by rw [← hGood.2.1]; exact_mod_cast hne.card_pos
  have hsum := witness_total_weight_bound (d := d) (r := 1) G (by norm_num : 2 ≤ 4) hm
    (show 0 ≤ C by linarith) hx
  apply (hcover.trans hsample).trans
  change (1/(G.card : ℝ))*(∑ W, w W) ≤ _
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1/(G.card : ℝ))).trans_eq
  rw [hGood.2.1]
  dsimp only [x]
  field_simp [ne_of_gt hmpos]
  ring

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

end

end OAI
