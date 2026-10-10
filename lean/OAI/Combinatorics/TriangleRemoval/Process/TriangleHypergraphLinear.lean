import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraph
import OAI.Combinatorics.TriangleRemoval.Spectral.TracedGridQuerySeparated
import OAI.Combinatorics.TriangleRemoval.Spectral.TracedGridQueryAddress

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem triangleHypergraph_linear {n : ℕ} (G : Graph n)
    (T S : Finset (Fin n)) (hTS : T ≠ S) :
    (triangleHypergraph G T ∩ triangleHypergraph G S).card ≤ 1 := by
  by_cases hT : T ∈ triangles G
  · by_cases hS : S ∈ triangles G
    · simp only [triangleHypergraph, hT, hS, ↓reduceIte]
      apply Finset.card_le_one.mpr
      intro e he f hf
      by_contra hef
      obtain ⟨heT,heS⟩ := Finset.mem_inter.mp he
      obtain ⟨hfT,hfS⟩ := Finset.mem_inter.mp hf
      obtain ⟨heT,hce⟩ := Finset.mem_powersetCard.mp heT
      obtain ⟨hfT,hcf⟩ := Finset.mem_powersetCard.mp hfT
      have heS := (Finset.mem_powersetCard.mp heS).1
      have hfS := (Finset.mem_powersetCard.mp hfS).1
      exact hTS (triangle_eq_of_two_edges (mem_triangles.mp hT).1
        (mem_triangles.mp hS).1 hce hcf hef heT hfT heS hfS)
    · simp [triangleHypergraph, hS]
  · simp [triangleHypergraph, hT]

lemma disjoint_edges_not_same_triangle {α : Type*} [DecidableEq α]
    {T e f : Finset α} (hT : T.card = 3)
    (he : e ∈ T.powersetCard 2) (hf : f ∈ T.powersetCard 2)
    (hd : Disjoint e f) : False := by
  obtain ⟨he,hce⟩ := Finset.mem_powersetCard.mp he
  obtain ⟨hf,hcf⟩ := Finset.mem_powersetCard.mp hf
  have hh := Finset.card_le_card (Finset.union_subset he hf)
  rw [Finset.card_union_of_disjoint hd,hce,hcf,hT] at hh
  omega

theorem triangleHypergraph_separated_disjoint_roots {n : ℕ} (G : Graph n)
    (e f : Finset (Fin n)) (hd : Disjoint e f) :
    (QueryCall.mk [] {e,f} none).Separated (triangleHypergraph G) := by
  intro T _
  by_cases hT : T ∈ triangles G
  · change (triangleHypergraph G T ∩ {e,f}).card ≤ 1
    simp only [triangleHypergraph,hT,↓reduceIte]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haT,haR⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbT,hbR⟩ := Finset.mem_inter.mp hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at haR hbR
    rcases haR with rfl | rfl <;> rcases hbR with rfl | rfl
    · rfl
    · exact False.elim (disjoint_edges_not_same_triangle (mem_triangles.mp hT).1 haT hbT hd)
    · exact False.elim (disjoint_edges_not_same_triangle (mem_triangles.mp hT).1 hbT haT hd)
    · rfl
  · simp [triangleHypergraph,hT]

theorem graph_query_repeat_addresses {n : ℕ} (G : Graph n) (N d k : ℕ)
    (c : QueryCall (Finset (Fin n)) (Finset (Fin n)))
    (hc : c.Separated (triangleHypergraph G))
    (ν : Finset (Fin n) → PMF (Fin N))
    {z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n))}
    (hz : z ∈ (ExposureTree.freshLog ν
      (tracedGridQuery (triangleHypergraph G) N d k c)).support)
    (hr : ExposureTree.repeats ∅ z.2 = true) :
    ∃ a ∈ z.1.2, ∃ b ∈ z.1.2, a.address ≠ b.address ∧ ∃ T,
      T ∈ a.keys (triangleHypergraph G) ∧ T ∈ b.keys (triangleHypergraph G) := by
  obtain ⟨i,j,hij,T,hi,hj⟩ := tracedGridQuery_repeat_calls _
    (triangleHypergraph_linear G) N d k c hc ν hz hr
  have hnd := tracedGridQuery_address_nodup _ N d k c ν hz
  have hpair : z.1.2.Pairwise (fun a b => a.address ≠ b.address) := by
    simpa only [List.Nodup,List.pairwise_map] using hnd
  exact ⟨z.1.2.get i, List.get_mem _ _, z.1.2.get j, List.get_mem _ _,
    List.pairwise_iff_get.mp hpair i j hij, T, hi, hj⟩

end SharpTerminalLeave

end

end OAI
