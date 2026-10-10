import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.WitnessEmbeddingBound
import OAI.Combinatorics.TriangleRemoval.Embeddings.EmbeddedWitnessRoots

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

theorem rooted_counted_traced_repeat_cover (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
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
      WitnessEmbeddingBound focus.card W ∧ embeddedWitnessRoots W = focus ∧
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
  have hroots : embeddedWitnessRoots W = focus := by
    change (A.pathRootEdges a b).image (Finset.image (A.pathAssignment a b hi)) = c.focus
    exact (A.pathRootEdges_image a b hi).trans (F.growth_seed_image hM hG)
  exact ⟨W,hbound,hroots,⟨F.call (F.vertexCall a),List.get_mem z.1.2 _,hleft.symm⟩,
    ⟨F.call (F.vertexCall b),List.get_mem z.1.2 _,hright.symm⟩⟩

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable instance rootedCountedTracedRepeatIndexedWitnessCodeFintype
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
