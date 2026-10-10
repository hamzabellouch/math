import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.CanonicalCollisionSum
import OAI.Combinatorics.TriangleRemoval.Process.IndexedWitnessCodeCard
import OAI.Combinatorics.TriangleRemoval.Process.WitnessDimensionEquiv
import OAI.Combinatorics.TriangleRemoval.Probability.UniformDistinctRootSet

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

lemma EdgeMatching.card_biUnion {V : Type*} [DecidableEq V]
    {E : Finset (Finset V)} (h : EdgeMatching E) :
    (E.biUnion id).card = 2*E.card := by
  change (E.biUnion (fun e => e)).card = _
  rw [Finset.card_biUnion h.2]
  calc
    _ = ∑ _e ∈ E, 2 := Finset.sum_congr rfl (fun e he => h.1 e he)
    _ = _ := by simp only [Finset.sum_const,smul_eq_mul,Nat.mul_comm]

lemma disjoint_valid_edge_ne {n : ℕ} {e f : Finset (Fin n)}
    (he : e.card = 2) (hd : Disjoint e f) : e ≠ f := by
  rintro rfl
  have h : e = ∅ := disjoint_self.mp hd
  rw [h,Finset.card_empty] at he
  omega

theorem canonical_collision_pair_sum (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (e f : Finset (Fin n)), e ∈ G → f ∈ G → Disjoint e f →
    ∀ (N : ℕ) [NeZero N] (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t)
    (_hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
    tracedCollisionProbability (triangleHypergraph G) N d k {e,f} none ≤
      ∑ W : BoundedEmbeddedWitness G 4 d,
        if WitnessEmbeddingBound 2 W ∧ embeddedWitnessRoots W = {e,f} then
          C^3 * ((3*prefixWeight (fun t => (2/(N : ℝ))*b t) k)^W.1.val.2.val /
            (W.1.val.2.val.factorial : ℝ)) else 0 := by
  classical
  filter_upwards [canonical_collision_sum c₀ C₀ hc₀] with n hn
  intro G hGood e f he hf hd N _ b hb hq C hC hlower d k hkd hkN
  have he2 := mem_completeGraph.mp (hGood.1 he)
  have hf2 := mem_completeGraph.mp (hGood.1 hf)
  have hm := EdgeMatching.pair e f he2 hf2 hd
  have hef : e ≠ f := disjoint_valid_edge_ne he2 hd
  have hcard : ({e,f} : Graph n).card = 2 := Finset.card_pair hef
  have hbi : (({e,f} : Graph n).biUnion id).card = 4 := by
    rw [hm.card_biUnion,hcard]
  have hh := hn G hGood {e,f} none hm (by intro a ha; simp only [Finset.mem_insert,Finset.mem_singleton] at ha; rcases ha with rfl | rfl <;> assumption)
    (by rw [hcard]) (triangleHypergraph_separated_disjoint_roots G e f hd)
    N b hb hq C hC hlower d k hkd hkN
  rw [hbi] at hh
  simpa only [hcard] using hh

lemma witness_total_weight_bound {n R d r : ℕ} (G : Graph n) (hR : R ≤ 4)
    (hm : 0 ≤ prefixM n) {C x : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) :
    (∑ W : BoundedEmbeddedWitness G R d, if WitnessEmbeddingBound r W then
      C^3*((3*x)^W.1.val.2.val/(W.1.val.2.val.factorial : ℝ)) else 0) ≤
      (2048*(4*prefixM n)^r*C^3/prefixD n^50)*Real.exp (45*prefixD n*x) := by
  have hD : 0 ≤ prefixD n := by unfold prefixD; positivity
  apply (boundedEmbeddedWitness_weight_sum G r hR hm
    (fun q => C^3*((3*x)^q.val.2.val/(q.val.2.val.factorial : ℝ)))
    (fun _ => by positivity)).trans
  exact witness_dimensions_weight_sum hR hm hD hC hx

theorem averaged_disjoint_grid_collision (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (hne : G.Nonempty) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t) (_hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if Disjoint e f then
        tracedCollisionProbability (triangleHypergraph G) N d k {e,f} none else 0)) ≤
      (65536*C^3/prefixD n^50)*
        Real.exp (45*prefixD n*prefixWeight (fun t => (2/(N : ℝ))*b t) k) := by
  classical
  filter_upwards [canonical_collision_pair_sum c₀ C₀ hc₀] with n hn
  intro G hGood hne N _ b hb hq C hC hlower d k hkd hkN
  let x := prefixWeight (fun t => (2/(N : ℝ))*b t) k
  have hx : 0 ≤ x := by
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (by positivity) (hb t)
  let w (W : BoundedEmbeddedWitness G 4 d) : ℝ :=
    if WitnessEmbeddingBound 2 W then C^3*((3*x)^W.1.val.2.val/(W.1.val.2.val.factorial : ℝ)) else 0
  have hw (W : BoundedEmbeddedWitness G 4 d) : 0 ≤ w W := by
    dsimp only [w]
    split_ifs <;> positivity
  have hcover : pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if Disjoint e f then
        tracedCollisionProbability (triangleHypergraph G) N d k {e,f} none else 0)) ≤
      pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f =>
        ∑ W : BoundedEmbeddedWitness G 4 d,
          if e ≠ f ∧ embeddedWitnessRoots W = {e,f} then w W else 0)) := by
    apply pmfMean_mono
    intro e he
    apply pmfMean_mono
    intro f hf
    have heG := (PMF.mem_support_uniformOfFinset_iff hne e).mp he
    have hfG := (PMF.mem_support_uniformOfFinset_iff hne f).mp hf
    by_cases hd : Disjoint e f
    · rw [ite_eq_left hd]
      have hef : e ≠ f := disjoint_valid_edge_ne (mem_completeGraph.mp (hGood.1 heG)) hd
      have hh := hn G hGood e f heG hfG hd N b hb hq C hC hlower d k hkd hkN
      apply hh.trans_eq
      apply Finset.sum_congr rfl
      intro W _
      by_cases hW : WitnessEmbeddingBound 2 W <;>
        by_cases hroot : embeddedWitnessRoots W = {e,f} <;>
          simp [w,x,hef,hW,hroot]
    · rw [ite_eq_right hd]
      apply Finset.sum_nonneg
      intro W _
      split_ifs <;> first | exact hw W | rfl
  have hsample := uniform_two_root_weighted_sum G hne embeddedWitnessRoots w hw
  have hm : 0 ≤ prefixM n := by rw [← hGood.2.1]; positivity
  have hmpos : 0 < prefixM n := by rw [← hGood.2.1]; exact_mod_cast hne.card_pos
  have hsum := witness_total_weight_bound (d := d) (r := 2) G (by norm_num : 4 ≤ 4) hm
    (show 0 ≤ C by linarith) hx
  apply (hcover.trans hsample).trans
  change (2/(G.card : ℝ)^2)*(∑ W, w W) ≤ _
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2/(G.card : ℝ)^2)).trans_eq
  rw [hGood.2.1]
  dsimp only [x]
  field_simp [ne_of_gt hmpos]
  ring

end SharpTerminalLeave

end

end OAI
