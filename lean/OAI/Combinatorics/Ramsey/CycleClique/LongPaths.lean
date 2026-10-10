import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.ColouredPaths

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem path_close_cycle {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hlen : 2 ≤ p.length) (hyx : G.Adj y x) :
    (SimpleGraph.Walk.cons hyx p).IsCycle := by
  apply (p.cons_isCycle_iff hyx).mpr
  refine ⟨hp, ?_⟩
  intro he
  have hn := hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using he)
  omega

 

theorem extend_nonspanning_cycle {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) {x : V} (c : G.Walk x x) (hc : c.IsCycle)
    (hout : ∃ z, z ∉ c.support) :
    ∃ u v, ∃ p : G.Walk u v, p.IsPath ∧ p.length = c.length := by
  classical
  obtain ⟨z, hz⟩ := hout
  obtain ⟨w⟩ := hconn.preconnected x z
  obtain ⟨d, _, hd, hdz⟩ := w.exists_boundary_dart {v | v ∈ c.support} c.start_mem_support hz
  let q := c.rotate d.fst hd
  have hq : q.IsCycle := hc.rotate hd
  have hlen : q.length = c.length := c.length_rotate _ _
  have hnot : d.snd ∉ q.tail.reverse.support := by
    intro hm
    have hm₁ : d.snd ∈ q.tail.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hm
    have hm₂ : d.snd ∈ q.support := q.isSubwalk_rfl.tail.support_subset hm₁
    exact hdz ((c.mem_support_rotate_iff _ _).mp hm₂)
  let p := SimpleGraph.Walk.cons d.adj.symm q.tail.reverse
  refine ⟨d.snd, _, p, ?_, ?_⟩
  · exact hq.isPath_tail.reverse.cons hnot
  · have hl := hc.three_le_length
    simp only [p, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.length_tail, hlen]
    omega

 

theorem long_path_min_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d) (hconn : G.Connected)
    (hdegree : ∀ v, d ≤ G.degree v) :
    ∃ x y, ∃ p : G.Walk x y, p.IsPath ∧ min (Fintype.card V) (2 * d + 1) ≤ p.length + 1 := by
  classical
  let : Nonempty V := hconn.nonempty
  obtain ⟨x, y, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨x, y, p, hp, ?_⟩
  by_contra hn
  have hlen : p.length < 2 * d := by omega
  have horder : p.length + 1 < Fintype.card V := by omega
  let W : Set V := {v | v ∈ p.support}
  have hWcard : W.ncard = p.length + 1 := by
    have heq : W = (p.support.toFinset : Set V) := by ext v; simp [W]
    rw [heq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support]
  have hnb : ∀ v, G.Adj y v → v ∈ p.support :=
    longest_path_endpoint_neighbors p hp (fun v q hq => hmax x v q hq)
  have hxnb : ∀ v, G.Adj x v → v ∈ p.support := by
    intro v hv
    have := longest_path_endpoint_neighbors p.reverse hp.reverse
      (fun v q hq => by simpa using hmax y v q hq) v hv
    simpa using this
  have hlower : d ≤ p.length := by
    have hc := degree_add_one_le_of_neighbors_subset (G := G) (v := y)
      (show y ∈ W from p.end_mem_support) (fun v hv => hnb v hv)
    rw [hWcard] at hc
    have := hdegree y
    omega
  let E := pathEnds G x p.support
  have hE : d ≤ E.ncard :=
    (hdegree y).trans (degree_le_card_pathEnds p hp (List.Perm.refl _) hnb)
  have hxE : x ∉ E := pathEnds_no_start (by rw [SimpleGraph.Walk.length_support]; omega)
  have hex : ∃ e, e ∈ E ∧ G.Adj x e := by
    by_contra hne
    push Not at hne
    have hdis : Disjoint E (G.neighborSet x) := by
      exact Set.disjoint_left.mpr (fun e he hn => hne e he hn)
    have hins : insert x (E ∪ G.neighborSet x) ⊆ W := by
      intro v hv
      rcases hv with rfl | hv
      · exact p.start_mem_support
      · rcases hv with hv | hv
        · exact mem_pathEnds_support hv
        · exact hxnb v hv
    have hnot : x ∉ E ∪ G.neighborSet x := by simp [hxE]
    have hc := Set.ncard_le_ncard hins
    rw [Set.ncard_insert_of_notMem hnot, Set.ncard_union_eq hdis,
      ncard_neighborSet, hWcard] at hc
    have hxdeg := hdegree x
    omega
  obtain ⟨e, he, hxe⟩ := hex
  obtain ⟨q, hq, hperm⟩ := he
  have hqlen : q.length = p.length := by
    have := hperm.length_eq
    simp only [SimpleGraph.Walk.length_support] at this
    omega
  let c := SimpleGraph.Walk.cons hxe.symm q
  have hc : c.IsCycle := path_close_cycle q hq (by omega) hxe.symm
  have hout : ∃ z, z ∉ c.support := by
    have hnW : W ≠ Set.univ := by
      intro heq
      rw [heq, Set.ncard_univ, Nat.card_eq_fintype_card] at hWcard
      omega
    have houtW : ∃ z, z ∉ W := by
      by_contra hh
      push Not at hh
      exact hnW (Set.eq_univ_of_forall hh)
    obtain ⟨z, hz⟩ := houtW
    refine ⟨z, ?_⟩
    intro hzc
    simp only [c, SimpleGraph.Walk.support_cons, List.mem_cons] at hzc
    rcases hzc with rfl | hzq
    · exact hz (hperm.mem_iff.mp q.end_mem_support)
    · exact hz (hperm.mem_iff.mp hzq)
  obtain ⟨u, v, R, hR, hRlen⟩ := extend_nonspanning_cycle hconn c hc hout
  have hh := hmax u v R hR
  simp only [c, SimpleGraph.Walk.length_cons, hqlen] at hRlen
  omega

end CycleClique

end OAI
