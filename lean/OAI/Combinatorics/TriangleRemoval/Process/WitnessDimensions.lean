import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.CallPath
import OAI.Combinatorics.TriangleRemoval.Queries.CallPathCollisionWitness
import OAI.Combinatorics.TriangleRemoval.Queries.Address
import OAI.Combinatorics.TriangleRemoval.Queries.MemAddressId
import OAI.Combinatorics.TriangleRemoval.Process.IndexedWitnessCode
import OAI.Combinatorics.TriangleRemoval.Process.MatchingSeedFullEdge
import OAI.Combinatorics.TriangleRemoval.Queries.VertexCall

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

abbrev WitnessDimensions (R d : ℕ) :=
  {q : Fin (R+2*d+1) × Fin (2*d+1) // q.1.val = R+q.2.val}

def dimensionBirth {R d : ℕ} (q : WitnessDimensions R d) : Fin q.val.2 → Fin q.val.1 :=
  fun i => ⟨R+i.val,by have hi := i.isLt; have hq := q.property; omega⟩

abbrev BoundedEmbeddedWitness {n : ℕ} (G : Graph n) (R d : ℕ) :=
  Σ q : WitnessDimensions R d,
    Σ E : {E : Graph q.val.1 // E ∈ seedPatternChoices q.val.1 R},
      Σ w : IndexedWitnessCode E.val (dimensionBirth q) (suffixProjection q.property),
        {ψ : Fin q.val.1 ↪ Fin n // ψ ∈ graphEmbeddingSet (decodeWitnessPattern w).2 G}

noncomputable instance {n : ℕ} (G : Graph n) (R d : ℕ) :
    Fintype (BoundedEmbeddedWitness G R d) := by
  classical
  unfold BoundedEmbeddedWitness
  infer_instance

def embeddedWitnessPaths {n R d : ℕ} {G : Graph n} (W : BoundedEmbeddedWitness G R d) :
    List (Finset (Fin n) × Finset (Fin n)) × List (Finset (Fin n) × Finset (Fin n)) :=
  let q := W.1
  let w := W.2.2.1
  let ψ := W.2.2.2.val
  let key := indexedTriangleKey (dimensionBirth q) w.2.2.val ψ
  ((suffixProjection q.property w.1.1).elim [] (w.2.1.val.address key) |>.reverse,
   (suffixProjection q.property w.1.2).elim [] (w.2.1.val.address key) |>.reverse)

theorem traced_repeat_canonical_cover {n : ℕ} (G focus : Graph n)
    (parent : Option (Finset (Fin n))) (hM : EdgeMatching focus) (hG : focus ⊆ G)
    (hr : focus.card ≤ 2)
    (hc : (QueryCall.mk [] focus parent).Separated (triangleHypergraph G))
    (N d k : ℕ) (ν : Finset (Fin n) → PMF (Fin N))
    (z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n)))
    (hz : z ∈ (ExposureTree.freshLog ν
      (tracedGridQuery (triangleHypergraph G) N d k ⟨[],focus,parent⟩)).support)
    (hrep : ExposureTree.repeats ∅ z.2 = true) :
    ∃ W : BoundedEmbeddedWitness G (focus.biUnion id).card d,
      (∃ a ∈ z.1.2, a.address = (embeddedWitnessPaths W).1.reverse) ∧
      (∃ b ∈ z.1.2, b.address = (embeddedWitnessPaths W).2.reverse) := by
  classical
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
  exact ⟨W,⟨F.call (F.vertexCall a),List.get_mem z.1.2 _,hleft.symm⟩,
    ⟨F.call (F.vertexCall b),List.get_mem z.1.2 _,hright.symm⟩⟩

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

end

end OAI
