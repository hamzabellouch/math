import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEpsilon
import OAI.Combinatorics.TriangleRemoval.Embeddings.GraphEmbeddings

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

def linkSimpleGraph {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    SimpleGraph (neighbors G u) where
  Adj x y := {x.val, y.val} ∈ G
  symm := ⟨by intro x y h; simpa only [Finset.pair_comm] using h⟩
  loopless := ⟨by
    intro x h
    have hh := mem_completeGraph.mp (hG h)
    simp at hh⟩

instance linkSimpleGraph_decidable {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    DecidableRel (linkSimpleGraph G hG u).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ G))

@[simp] theorem linkSimpleGraph_adj {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v w : neighbors G u) :
    (linkSimpleGraph G hG u).Adj v w ↔ {v.val,w.val} ∈ G := Iff.rfl

theorem cycleNext_eq_add_one {j : ℕ} (i : Fin (j+2)) : cycleNext i = i + 1 := by
  apply Fin.ext
  simp [cycleNext, Fin.add_def]

theorem cycleGraph_adj_next {j : ℕ} (i k : Fin (j+2)) :
    (SimpleGraph.cycleGraph (j+2)).Adj i k ↔ i = cycleNext k ∨ k = cycleNext i := by
  rw [SimpleGraph.cycleGraph_adj]
  simp only [cycleNext_eq_add_one, sub_eq_iff_eq_add, add_comm]

theorem link_neighbor_map {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) :
    (Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).map
      (Function.Embedding.subtype _) = commonNeighbors G u v.val := by
  ext w
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    linkSimpleGraph_adj, mem_commonNeighbors, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(Finset.mem_filter.mp x.property).2,hx⟩
  · rintro ⟨hu,hv⟩
    exact ⟨⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩,hv,rfl⟩

theorem link_degree_eq {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v : neighbors G u) :
    (Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).card = currentCodegree G u v.val := by
  rw [← Finset.card_map (Function.Embedding.subtype _), link_neighbor_map]
  rfl

theorem linkCycleCount_eq_graphEmbeddings {n j : ℕ} (G : Graph n)
    (hG : G ⊆ completeGraph n) (u : Fin n) :
    linkCycleCount (j+2) G u =
      ((graphEmbeddings (SimpleGraph.cycleGraph (j+2)) (linkSimpleGraph G hG u)).card : ℝ) := by
  classical
  let S : Finset (Fin (j+2) ↪ Fin n) := Finset.univ.filter (fun φ =>
    ∀ i, {u,φ i} ∈ G ∧ {φ i,φ (cycleNext i)} ∈ G)
  have heq : linkCycleCount (j+2) G u = (S.card : ℝ) := by
    simp [linkCycleCount,S,Finset.sum_boole]
  rw [heq]
  congr 1
  symm
  apply Finset.card_bij (fun (f : Fin (j+2) ↪ neighbors G u) _ =>
    f.trans (Function.Embedding.subtype _))
  · intro f hf
    have hf' := (mem_graphEmbeddings f).mp hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun i => ⟨?_,?_⟩⟩
    · exact (Finset.mem_filter.mp (f i).property).2
    · exact hf' i (cycleNext i) ((cycleGraph_adj_next i (cycleNext i)).mpr (Or.inr rfl))
  · intro f hf g hg hfg
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun (e : Fin (j+2) ↪ Fin n) => e i) hfg
  · intro φ hφ
    have hφ' := (Finset.mem_filter.mp hφ).2
    let f : Fin (j+2) ↪ neighbors G u :=
      ⟨fun i => ⟨φ i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hφ' i).1⟩⟩,
        fun a b h => φ.injective (congrArg Subtype.val h)⟩
    refine ⟨f,?_,?_⟩
    · apply (mem_graphEmbeddings f).mpr
      intro a b hab
      rcases (cycleGraph_adj_next a b).mp hab with hab | hab
      · change {φ a,φ b} ∈ G
        rw [hab,Finset.pair_comm]
        exact (hφ' b).2
      · change {φ a,φ b} ∈ G
        rw [hab]
        exact (hφ' a).2
    · rfl

theorem goodPrefix_link_rows {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (u : Fin n) (v : neighbors G u) :
    |(((Finset.univ.filter ((linkSimpleGraph G h.1 u).Adj v)).card : ℝ) - prefixD n)| ≤
      (n : ℝ)^(-c) * prefixD n := by
  rw [link_degree_eq]
  apply h.2.2.2.1
  intro heq
  have hv : {u,v.val} ∈ G := (Finset.mem_filter.mp v.property).2
  have hh := mem_completeGraph.mp (h.1 hv)
  simp [← heq] at hh

end SharpTerminalLeave

end
end

end OAI
