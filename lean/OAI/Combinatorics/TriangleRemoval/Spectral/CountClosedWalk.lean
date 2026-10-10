import Mathlib

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

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem bridge_count_closedWalk {a : V} (p : G.Walk a a) {e : Sym2 V}
    (he : e ∈ p.edges) (hb : G.IsBridge e) : 2 ≤ p.edges.count e := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨i, hi, heq⟩ := (p.mk_mem_edges_iff_exists).mp he
    let q := p.drop i
    have hq : ¬ q.Nil := by
      rw [← SimpleGraph.Walk.length_eq_zero_iff]
      dsimp [q]
      rw [SimpleGraph.Walk.drop_length]
      omega
    have he' : s(p.getVert i, q.snd) = s(x,y) := by
      simpa only [q, SimpleGraph.Walk.snd, SimpleGraph.Walk.drop_getVert] using heq
    have hmem : s(p.getVert i, q.snd) ∈ (q.tail.append (p.take i)).edges := by
      have hh : G.IsBridge s(p.getVert i, q.snd) := he'.symm ▸ hb
      have hwalk := (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp hh)
        (q.tail.append (p.take i)).reverse
      simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hwalk
    have hcount : 1 ≤ (q.tail.append (p.take i)).edges.count s(x,y) := by
      exact List.one_le_count_iff.mpr (he' ▸ hmem)
    have hp : p.edges = (p.take i).edges ++ s(x,y) :: q.tail.edges := by
      conv_lhs => rw [← p.append_take_drop_eq i]
      rw [SimpleGraph.Walk.edges_append]
      change (p.take i).edges ++ q.edges = _
      rw [← q.cons_tail_eq hq, SimpleGraph.Walk.edges_cons, he']
      simp
    rw [SimpleGraph.Walk.edges_append, List.count_append] at hcount
    rw [hp, List.count_append, List.count_cons_self]
    omega

theorem acyclic_closedWalk_distinct_edges {a : V} (p : G.Walk a a)
    (hG : G.IsAcyclic) : 2 * p.edges.toFinset.card ≤ p.length := by
  classical
  have hh : ∀ e ∈ p.edges.toFinset, 2 ≤ p.edges.count e := by
    intro e he
    have he' := List.mem_toFinset.mp he
    exact bridge_count_closedWalk p he'
      ((SimpleGraph.isAcyclic_iff_forall_isBridge.mp hG) (p.edges_subset_edgeSet he'))
  calc
    _ = ∑ _e ∈ p.edges.toFinset, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ e ∈ p.edges.toFinset, p.edges.count e := Finset.sum_le_sum hh
    _ = p.edges.length := by exact List.sum_toFinset_count_eq_length _
    _ = p.length := p.length_edges

theorem walk_support_card_le_edges {a b : V} (p : G.Walk a b) :
    p.support.toFinset.card ≤ p.edges.toFinset.card + 1 := by
  classical
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.edges_cons,
      List.toFinset_cons]
    by_cases ha : a ∈ p.support.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      exact ih.trans (Nat.add_le_add_right (Finset.card_le_card (Finset.subset_insert _ _)) 1)
    · have he : s(a,b) ∉ p.edges.toFinset := by
        intro he
        exact ha (List.mem_toFinset.mpr
          (p.fst_mem_support_of_mem_edges (List.mem_toFinset.mp he)))
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem he]
      omega

theorem acyclic_spanning_walk_vertices [Fintype V] {a : V} (p : G.Walk a a)
    (hG : G.IsAcyclic) (hspan : ∀ v, v ∈ p.support) :
    Fintype.card V - 1 ≤ p.length / 2 := by
  have hc := acyclic_closedWalk_distinct_edges p hG
  have hv := walk_support_card_le_edges p
  have hs : p.support.toFinset = Finset.univ := by
    exact Finset.eq_univ_iff_forall.mpr (fun v => List.mem_toFinset.mpr (hspan v))
  rw [hs, Finset.card_univ] at hv
  omega

end SharpTerminalLeave

end
end

end OAI
