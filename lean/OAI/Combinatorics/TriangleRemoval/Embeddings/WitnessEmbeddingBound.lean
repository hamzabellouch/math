import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.WitnessDimensions
import OAI.Combinatorics.TriangleRemoval.Process.WitnessCountEventually

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

def WitnessEmbeddingBound {n R d : ℕ} {G : Graph n}
    (r : ℕ) (W : BoundedEmbeddedWitness G R d) : Prop :=
  ((graphEmbeddingSet (decodeWitnessPattern W.2.2.1).2 G).card : ℝ) ≤
    (4*prefixM n)^r * (2*prefixD n)^W.1.val.2.val / prefixD n^50

lemma actual_witness_count_roots_eventually (c C : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c C G →
    ∀ r : ℕ, r ≤ 2 → ∀ N R : ℕ, ∀ (A : TriangleGrowth (lookupGraph G) N R),
      R ≤ N → R = 2*r → (A.seed.backEdges A.roots).card = r →
    ∀ a b : Fin N, A.birthGraph.ExtraEdge (lookupGraph G) A.label a b →
    ((graphEmbeddingSet (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
      ((A.pathPattern a b).backEdges Finset.univ)) G).card : ℝ) ≤
      (4*prefixM n)^r * (2*prefixD n)^(A.pathSuffix a b R).card / prefixD n^50 := by
  filter_upwards [actual_witness_count_eventually c C hc] with n hn
  intro G hG r hr N R A hR hRr hseed a b he
  subst R
  exact hn G hG r hr N A hR hseed a b he

theorem counted_traced_repeat_cover (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (focus : Graph n)
    (parent : Option (Finset (Fin n))) (_hM : EdgeMatching focus) (_hG : focus ⊆ G)
    (_hr : focus.card ≤ 2)
    (_hc : (QueryCall.mk [] focus parent).Separated (triangleHypergraph G))
    (N d k : ℕ) (ν : Finset (Fin n) → PMF (Fin N))
    (z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n)))
    (_hz : z ∈ (ExposureTree.freshLog ν
      (tracedGridQuery (triangleHypergraph G) N d k ⟨[],focus,parent⟩)).support)
    (_hrep : ExposureTree.repeats ∅ z.2 = true),
    ∃ W : BoundedEmbeddedWitness G (focus.biUnion id).card d,
      WitnessEmbeddingBound focus.card W ∧
      (∃ a ∈ z.1.2, a.address = (embeddedWitnessPaths W).1.reverse) ∧
      (∃ b ∈ z.1.2, b.address = (embeddedWitnessPaths W).2.reverse) := by
  classical
  filter_upwards [actual_witness_count_roots_eventually c₀ C₀ hc₀] with n hn
  intro G hGood focus parent hM hG hr hc N d k ν z hz hrep
  let c : QueryCall (Finset (Fin n)) (Finset (Fin n)) := ⟨[],focus,parent⟩
  let F := extractCallForest (triangleHypergraph G) N d k c ν z hz
  let A := F.toTriangleGrowth hM hG
  have hR : F.rootCount ≤ F.vertexCount := Nat.le_add_right _ _
  obtain ⟨a,b,he,hi⟩ := traced_graph_path_collision_witness G N d k c hM hG hc ν z hz hrep
  have hdepth (i : Fin F.size) : (F.call i).address.length ≤ d := by
    obtain ⟨p,hp,he⟩ := tracedGridQuery_legal_path (triangleHypergraph G) N d k c ν hz
      (F.call i) (List.get_mem z.1.2 i)
    rw [he,callAtPath_address]
    simpa only [c,List.append_nil,List.length_reverse] using
      (mem_legalPaths (triangleHypergraph G) d focus parent p).mp hp |>.2
  let key := indexedTriangleKey (A.pathBirthIndex a b hR) (A.pathAttachments a b hR)
    (A.pathAssignment a b hi)
  have hs : (A.pathSuffix a b F.rootCount).card ≤ 2*d := by
    have h := (A.pathForest a b).two_mark_size key
      (suffixProjection (A.path_card_split a b hR) (A.pathIndex a b a (A.left_mem_pathUnion a b)))
      (suffixProjection (A.path_card_split a b hR) (A.pathIndex a b b (A.right_mem_pathUnion a b)))
      (A.pathWitnessCode a b hR).2.1.property
    rw [F.decoded_mark_address hM hG rfl a b hR hi a (A.left_mem_pathUnion a b),
      F.decoded_mark_address hM hG rfl a b hR hi b (A.right_mem_pathUnion a b)] at h
    have ha := hdepth (F.vertexCall a)
    have hb := hdepth (F.vertexCall b)
    omega
  let q : WitnessDimensions F.rootCount d :=
    ⟨(⟨(A.pathUnion a b).card,by rw [A.path_card_split a b hR]; omega⟩,
      ⟨(A.pathSuffix a b F.rootCount).card,by omega⟩),A.path_card_split a b hR⟩
  have hseed : (A.seed.backEdges A.roots).card ≤ 2 := by
    rw [F.growth_seed_card hM hG]
    exact hr
  let E : {E : Graph (A.pathUnion a b).card // E ∈ seedPatternChoices (A.pathUnion a b).card F.rootCount} :=
    ⟨A.pathRootEdges a b,A.pathRootEdges_mem_seedPatternChoices a b hR hseed⟩
  let W : BoundedEmbeddedWitness G F.rootCount d :=
    ⟨q,E,A.pathWitnessCode a b hR,A.pathAssignment a b hi,A.pathAssignment_mem_decoded hR hi he⟩
  have hleft : (embeddedWitnessPaths W).1.reverse = (F.call (F.vertexCall a)).address := by
    change (((suffixProjection (A.path_card_split a b hR)
      (A.pathIndex a b a (A.left_mem_pathUnion a b))).elim []
      ((A.pathForest a b).address key)).reverse).reverse = _
    rw [List.reverse_reverse]
    exact F.decoded_mark_address hM hG rfl a b hR hi a (A.left_mem_pathUnion a b)
  have hright : (embeddedWitnessPaths W).2.reverse = (F.call (F.vertexCall b)).address := by
    change (((suffixProjection (A.path_card_split a b hR)
      (A.pathIndex a b b (A.right_mem_pathUnion a b))).elim []
      ((A.pathForest a b).address key)).reverse).reverse = _
    rw [List.reverse_reverse]
    exact F.decoded_mark_address hM hG rfl a b hR hi b (A.right_mem_pathUnion a b)
  have hbound : WitnessEmbeddingBound focus.card W := by
    have hh := hn G hGood focus.card hr F.vertexCount F.rootCount A hR
      (F.rootCount_focus_card hM) (F.growth_seed_card hM hG) a b he
    change ((graphEmbeddingSet (decodeWitnessPattern (A.pathWitnessCode a b hR)).2 G).card : ℝ) ≤
      (4*prefixM n)^focus.card*(2*prefixD n)^(A.pathSuffix a b F.rootCount).card/prefixD n^50
    change ((graphEmbeddingSet (insert {A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)}
      (indexedPatternEdges (A.pathRootEdges a b) (A.pathBirthIndex a b hR)
        (A.pathAttachments a b hR))) G).card : ℝ) ≤ _
    rw [← A.pathPattern_edges a b hR]
    exact hh
  exact ⟨W,hbound,⟨F.call (F.vertexCall a),List.get_mem z.1.2 _,hleft.symm⟩,
    ⟨F.call (F.vertexCall b),List.get_mem z.1.2 _,hright.symm⟩⟩

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable instance instFintypeIndexedWitnessCodeEmbeddingBound {K s : ℕ}
    (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Fintype (IndexedWitnessCode E birth mark) := by
  classical
  unfold IndexedWitnessCode
  infer_instance

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

end

end OAI
