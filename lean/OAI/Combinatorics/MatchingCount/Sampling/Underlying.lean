import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Components

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

namespace Overlay

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)

def underlying (M : Finset E) : SimpleGraph V where
  Adj v w := ∃ e ∈ M, ends e = s(v, w)
  symm := ⟨by
    rintro v w ⟨e, he, h⟩
    exact ⟨e, he, h.trans Sym2.eq_swap⟩⟩
  loopless := ⟨by
    rintro v ⟨e, he, h⟩
    exact hloop e (by rw [h]; simp)⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma exists_partner {e : E} {v : V} (hv : v ∈ ends e) :
    ∃ w, ends e = s(v,w) := by
  exact hv

omit [DecidableEq V] [DecidableEq E] in
lemma underlying_perfect [DecidableEq V] [DecidableEq E] (M : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ) :
    (SimpleGraph.toSubgraph (G := ⊤) (underlying ends hloop M) le_top).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  obtain ⟨e, ⟨he, hev⟩, heuniq⟩ := hM.2 v (Finset.mem_univ v)
  obtain ⟨w, hw⟩ := exists_partner ends hev
  refine ⟨w, ⟨e, he, hw⟩, ?_⟩
  rintro u ⟨f, hf, hfu⟩
  have hfv : v ∈ ends f := by rw [hfu]; simp
  have hfe := heuniq f ⟨hf, hfv⟩
  have hsym : s(v,u) = s(v,w) := hfu.symm.trans ((congrArg ends hfe).trans hw)
  have h : u = w ∨ v = w ∧ u = v := by simpa using hsym
  exact h.elim id (fun h => h.2.trans h.1)

open scoped symmDiff

def discrepancy (M N : Finset E) : SimpleGraph V :=
  underlying ends hloop M ∆ underlying ends hloop N

lemma discrepancy_cycles (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ) :
    (discrepancy ends hloop M N).IsCycles := by
  have h := (underlying_perfect ends hloop M hM).symmDiff_isCycles
    (underlying_perfect ends hloop N hN)
  exact h

lemma discrepancy_alternating (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ) :
    (discrepancy ends hloop M N).IsAlternating (underlying ends hloop M) := by
  have h := (underlying_perfect ends hloop M hM).isAlternating_symmDiff_left
    (underlying_perfect ends hloop N hN)
  exact h

lemma discrepancy_component_cycle (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    (c : (discrepancy ends hloop M N).ConnectedComponent) (v : V)
    (hv : v ∈ c.supp) (hn : ((discrepancy ends hloop M N).neighborSet v).Nonempty) :
    ∃ p : (discrepancy ends hloop M N).Walk v v,
      p.IsCycle ∧ p.toSubgraph.verts = c.supp :=
  (discrepancy_cycles ends hloop M N hM hN).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma discrepancy_adj_iff [Fintype V] [DecidableEq V] [DecidableEq E] (M N : Finset E) (v w : V) :
    (discrepancy ends hloop M N).Adj v w ↔
      ((underlying ends hloop M).Adj v w ∧ ¬ (underlying ends hloop N).Adj v w) ∨
      ((underlying ends hloop N).Adj v w ∧ ¬ (underlying ends hloop M).Adj v w) := by
  rfl

lemma unique_colored_lift (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    {v w : V} (hadj : (discrepancy ends hloop M N).Adj v w) :
    ∃! e, e ∈ M ∪ N ∧ ends e = s(v,w) := by
  rcases (discrepancy_adj_iff ends hloop M N v w).mp hadj with h | h
  · obtain ⟨e, he, hend⟩ := h.1
    refine ⟨e, ⟨Finset.mem_union_left N he, hend⟩, ?_⟩
    rintro f ⟨hf, hfend⟩
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨g, hg, hu⟩ := hM.2 v (Finset.mem_univ v)
      exact (hu f ⟨hf, by change v ∈ ends f; rw [hfend]; simp⟩).trans
        (hu e ⟨he, by change v ∈ ends e; rw [hend]; simp⟩).symm
    · exact (h.2 ⟨f, hf, hfend⟩).elim
  · obtain ⟨e, he, hend⟩ := h.1
    refine ⟨e, ⟨Finset.mem_union_right M he, hend⟩, ?_⟩
    rintro f ⟨hf, hfend⟩
    rcases Finset.mem_union.mp hf with hf | hf
    · exact (h.2 ⟨f, hf, hfend⟩).elim
    · obtain ⟨g, hg, hu⟩ := hN.2 v (Finset.mem_univ v)
      exact (hu f ⟨hf, by change v ∈ ends f; rw [hfend]; simp⟩).trans
        (hu e ⟨he, by change v ∈ ends e; rw [hend]; simp⟩).symm

lemma colored_lift_mem_iff (M N : Finset E)
    {v w : V} (hadj : (discrepancy ends hloop M N).Adj v w)
    {e : E} (he : e ∈ M ∪ N) (hend : ends e = s(v,w)) :
    (e ∈ M ↔ (underlying ends hloop M).Adj v w) ∧
    (e ∈ N ↔ (underlying ends hloop N).Adj v w) := by
  rcases (discrepancy_adj_iff ends hloop M N v w).mp hadj with h | h
  · have hen : e ∉ N := fun hen => h.2 ⟨e, hen, hend⟩
    have hem : e ∈ M := (Finset.mem_union.mp he).resolve_right hen
    simp only [hem, hen, h.1, h.2, and_self]
  · have hem : e ∉ M := fun hem => h.2 ⟨e, hem, hend⟩
    have hen : e ∈ N := (Finset.mem_union.mp he).resolve_left hem
    simp only [hem, hen, h.1, h.2, and_self]

omit [Fintype V] [DecidableEq V] in
lemma alternating_cycle_parity [Fintype V] [DecidableEq V] {G H : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (halt : G.IsAlternating H) :
    p.length % 2 = 0 := by
  let Q : ℕ → Prop := fun i => H.Adj (p.getVert i) (p.getVert (i + 1))
  have recur : ∀ i, i + 1 < p.length → (Q (i + 1) ↔ ¬ Q i) := by
    intro i hi
    have hn : p.getVert i ≠ p.getVert (i + 2) := by
      simpa using hp.getVert_sub_one_ne_getVert_add_one (i := i + 1) (by omega)
    have h := halt hn (p.adj_getVert_succ (i := i) (by omega)).symm
      (p.adj_getVert_succ (i := i + 1) hi)
    dsimp [Q]
    have hsym := H.adj_comm (u := p.getVert (i + 1)) (v := p.getVert i)
    tauto
  have parity : ∀ i, i < p.length →
      (Q i ↔ if i % 2 = 0 then Q 0 else ¬ Q 0) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      rw [recur i hi, ih (by omega)]
      split_ifs <;> first | omega | tauto
  have hn : p.getVert 1 ≠ p.getVert (p.length - 1) := by
    simpa [SimpleGraph.Walk.snd, SimpleGraph.Walk.penultimate] using hp.snd_ne_penultimate
  have hfirst := p.adj_getVert_succ (i := 0) (by have := hp.three_le_length; omega)
  have hlast := p.adj_getVert_succ (i := p.length - 1) (by have := hp.three_le_length; omega)
  have he : p.length - 1 + 1 = p.length := by have := hp.three_le_length; omega
  have hclose : Q 0 ↔ ¬ Q (p.length - 1) := by
    have h := halt hn (by simpa using hfirst) (by simpa [he] using hlast.symm)
    simpa [Q, he, H.adj_comm] using h
  have hr := parity (p.length - 1) (by have := hp.three_le_length; omega)
  split_ifs at hr
  · tauto
  · have := hp.three_le_length
    omega

lemma discrepancy_component_even_cycle (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    (c : (discrepancy ends hloop M N).ConnectedComponent) (v : V)
    (hv : v ∈ c.supp) (hn : ((discrepancy ends hloop M N).neighborSet v).Nonempty) :
    ∃ p : (discrepancy ends hloop M N).Walk v v,
      p.IsCycle ∧ p.toSubgraph.verts = c.supp ∧ p.length % 2 = 0 ∧ 4 ≤ p.length := by
  obtain ⟨p, hp, hc⟩ := discrepancy_component_cycle ends hloop M N hM hN c v hv hn
  have he := alternating_cycle_parity p hp (discrepancy_alternating ends hloop M N hM hN)
  exact ⟨p, hp, hc, he, by have := hp.three_le_length; omega⟩

def cyclicVertex {G : SimpleGraph V} {v : V} (p : G.Walk v v) (i : ℕ) : V :=
  p.getVert (i % p.length)

omit [Fintype V] [DecidableEq V] in
lemma cyclicVertex_periodic [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V} (p : G.Walk v v) (i : ℕ) :
    cyclicVertex p (i + p.length) = cyclicVertex p i := by
  simp [cyclicVertex]

omit [Fintype V] [DecidableEq V] in
lemma cyclicVertex_injOn [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) : Set.InjOn (cyclicVertex p) (Set.Ico 0 p.length) := by
  intro i hi j hj h
  have hi' := hi.2
  have hj' := hj.2
  simp only [cyclicVertex, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at h
  exact hp.getVert_injOn' (by change i ≤ p.length - 1; omega)
    (by change j ≤ p.length - 1; omega) h

omit [Fintype V] [DecidableEq V] in
lemma cyclicVertex_next [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (i : ℕ) (hi : i < p.length) : cyclicVertex p (i + 1) = p.getVert (i + 1) := by
  by_cases h : i + 1 < p.length
  · simp [cyclicVertex, Nat.mod_eq_of_lt h]
  · have he : i + 1 = p.length := by omega
    simp [he, cyclicVertex]

lemma cyclicVertex_adj {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) (i : ℕ) : G.Adj (cyclicVertex p i) (cyclicVertex p (i + 1)) := by
  have hm : i % p.length < p.length := Nat.mod_lt i (by have := hp.three_le_length; omega)
  have he : cyclicVertex p (i + 1) = cyclicVertex p (i % p.length + 1) := by
    simp only [cyclicVertex, Nat.add_mod, Nat.mod_mod]
  rw [he, cyclicVertex_next p _ hm]
  exact p.adj_getVert_succ hm

noncomputable def cyclicEdge (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    {v : V} (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle) (i : ℕ) : E :=
  (unique_colored_lift ends hloop M N hM hN (cyclicVertex_adj p hp i)).choose

lemma cyclicEdge_spec (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    {v : V} (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle) (i : ℕ) :
    cyclicEdge ends hloop M N hM hN p hp i ∈ M ∪ N ∧
      ends (cyclicEdge ends hloop M N hM hN p hp i) =
        s(cyclicVertex p i, cyclicVertex p (i + 1)) :=
  (unique_colored_lift ends hloop M N hM hN (cyclicVertex_adj p hp i)).choose_spec.1

lemma cyclicEdge_periodic (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    {v : V} (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle) (i : ℕ) :
    cyclicEdge ends hloop M N hM hN p hp (i + p.length) =
      cyclicEdge ends hloop M N hM hN p hp i := by
  have hs := cyclicEdge_spec ends hloop M N hM hN p hp (i + p.length)
  apply (unique_colored_lift ends hloop M N hM hN (cyclicVertex_adj p hp i)).choose_spec.2
  refine ⟨hs.1, ?_⟩
  simpa [cyclicVertex_periodic, show i + p.length + 1 = i + 1 + p.length by omega] using hs.2

end Overlay

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.Overlay

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)

variable (M N : Finset E)

variable (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)

variable (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)

noncomputable def indexedCycle {v : V}
    (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle) :
    IndexedCycle (fun e v => v ∈ ends e) where
  size := p.length
  four_le := by
    have hh := hp.three_le_length
    have he := alternating_cycle_parity p hp (discrepancy_alternating ends hloop M N hM hN)
    omega
  even := alternating_cycle_parity p hp (discrepancy_alternating ends hloop M N hM hN)
  vertex i := cyclicVertex p i.val
  simple := by
    intro i j h
    apply Fin.ext
    exact cyclicVertex_injOn p hp ⟨Nat.zero_le _, i.isLt⟩ ⟨Nat.zero_le _, j.isLt⟩ h
  edge i := cyclicEdge ends hloop M N hM hN p hp i.val
  incidence := by
    intro i w
    rw [(cyclicEdge_spec ends hloop M N hM hN p hp i.val).2]
    simp only [Sym2.mem_iff, cyclicVertex, Nat.mod_mod]

lemma indexedCycle_edge_mem {v : V}
    (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle)
    (i : Fin p.length) : (indexedCycle ends hloop M N hM hN p hp).edge i ∈ M ∪ N :=
  (cyclicEdge_spec ends hloop M N hM hN p hp i.val).1

lemma cyclicEdge_injective {v : V}
    (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle) :
    Set.InjOn (cyclicEdge ends hloop M N hM hN p hp) (Set.Ico 0 p.length) := by
  intro i hi j hj h
  have hi' : i < p.edges.length := by simpa using hi.2
  have hj' : j < p.edges.length := by simpa using hj.2
  apply (hp.isCircuit.isTrail.edges_nodup.getElem_inj_iff (hi := hi') (hj := hj')).mp
  rw [SimpleGraph.Walk.getElem_edges hi', SimpleGraph.Walk.getElem_edges hj']
  have hh := congrArg ends h
  rw [(cyclicEdge_spec ends hloop M N hM hN p hp i).2,
    (cyclicEdge_spec ends hloop M N hM hN p hp j).2] at hh
  rw [cyclicVertex_next p i hi.2, cyclicVertex_next p j hj.2] at hh
  simpa only [cyclicVertex, Nat.mod_eq_of_lt hi.2, Nat.mod_eq_of_lt hj.2] using hh

omit [Fintype V] [DecidableEq V] in
lemma alternating_edge_parity [Fintype V] [DecidableEq V] {G H : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (halt : G.IsAlternating H)
    (i : ℕ) (hi : i < p.length) :
    H.Adj (p.getVert i) (p.getVert (i+1)) ↔
      if i % 2 = 0 then H.Adj (p.getVert 0) (p.getVert 1)
      else ¬H.Adj (p.getVert 0) (p.getVert 1) := by
  let Q : ℕ → Prop := fun j => H.Adj (p.getVert j) (p.getVert (j+1))
  have recur : ∀ j, j + 1 < p.length → (Q (j + 1) ↔ ¬Q j) := by
    intro j hj
    have hn : p.getVert j ≠ p.getVert (j + 2) := by
      simpa using hp.getVert_sub_one_ne_getVert_add_one (i := j+1) (by omega)
    have h := halt hn (p.adj_getVert_succ (i := j) (by omega)).symm
      (p.adj_getVert_succ (i := j+1) hj)
    dsimp [Q]
    have hsym := H.adj_comm (u := p.getVert (j+1)) (v := p.getVert j)
    tauto
  change Q i ↔ if i % 2 = 0 then Q 0 else ¬Q 0
  induction i with
  | zero => simp
  | succ i ih =>
    rw [recur i hi, ih (by omega)]
    split_ifs <;> first | omega | tauto

lemma cyclicEdge_mem_parity {v : V}
    (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle)
    (i : ℕ) (hi : i < p.length) :
    cyclicEdge ends hloop M N hM hN p hp i ∈ M ↔
      if i % 2 = 0 then cyclicEdge ends hloop M N hM hN p hp 0 ∈ M
      else cyclicEdge ends hloop M N hM hN p hp 0 ∉ M := by
  have hi_spec := cyclicEdge_spec ends hloop M N hM hN p hp i
  have h0_spec := cyclicEdge_spec ends hloop M N hM hN p hp 0
  have hi_mem := (colored_lift_mem_iff ends hloop M N (cyclicVertex_adj p hp i)
    hi_spec.1 hi_spec.2).1
  have h0_mem := (colored_lift_mem_iff ends hloop M N (cyclicVertex_adj p hp 0)
    h0_spec.1 h0_spec.2).1
  rw [hi_mem, h0_mem]
  have hn : 0 < p.length := by have := hp.three_le_length; omega
  rw [cyclicVertex_next p i hi, cyclicVertex_next p 0 hn]
  simpa only [cyclicVertex, Nat.zero_mod, Nat.mod_eq_of_lt hi] using
    alternating_edge_parity p hp (discrepancy_alternating ends hloop M N hM hN) i hi

end

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)

variable {M N : Finset E}

variable (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)

variable (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)

include hM hN

omit [DecidableEq V] in
lemma parallel_component [DecidableEq V] {e f : E} (he : e ∈ M) (hf : f ∈ N)
    (hef : ends e = ends f) :
    componentEdges (inc := fun e v => v ∈ ends e) (M ∪ N) e = {e,f} := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, v ∈ ends e := by
    induction ends e using Sym2.inductionOn with | hf a b => exact ⟨a,by simp⟩
  have hfv : v ∈ ends f := hef ▸ hv
  have closed : ∀ {a b}, a ∈ ({e,f} : Finset E) →
      (overlayLineGraph (fun e v => v ∈ ends e) (M ∪ N)).Adj a b → b ∈ ({e,f} : Finset E) := by
    intro a b ha hab
    obtain ⟨_,_,hb,w,haw,hbw⟩ := hab
    have hew : w ∈ ends e := by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact haw
      · have haf := Finset.mem_singleton.mp ha
        simpa only [haf,← hef] using haw
    have hfw : w ∈ ends f := hef ▸ hew
    rcases Finset.mem_union.mp hb with hb | hb
    · have hbe := hM.unique (Finset.mem_univ w) hb hbw he hew
      simp [hbe]
    · have hbf := hN.unique (Finset.mem_univ w) hb hbw hf hfw
      simp [hbf]
  ext a
  constructor
  · intro ha
    obtain ⟨hau,hr⟩ := (mem_componentEdges _ _ _).mp ha
    have hrel := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hr
    clear ha hau hr
    induction hrel with
    | refl => simp
    | tail hpath hadj ih => exact closed ih hadj
  · intro ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact componentEdges_self (Finset.mem_union_left N he)
    · have haf := Finset.mem_singleton.mp ha
      subst a
      exact (mem_componentEdges _ _ _).mpr ⟨Finset.mem_union_right M hf,
        shares_reachable (Finset.mem_union_left N he) (Finset.mem_union_right M hf) hv hfv⟩

include hloop

theorem component_classification {S : Finset E}
    (hS : S ∈ components (inc := fun e v => v ∈ ends e) (M ∪ N)) :
    (∃ e ∈ M, ∃ f ∈ N, ends e = ends f ∧ S = {e,f}) ∨
    (∃ c : IndexedCycle (fun e v => v ∈ ends e),
      (∀ i, c.edgeAt i ∈ M ∪ N) ∧ S = c.edgeSet) := by
  classical
  obtain ⟨a,ha,haS⟩ := mem_components.mp hS
  obtain ⟨v,hav⟩ : ∃ v, v ∈ ends a := by
    induction ends a using Sym2.inductionOn with | hf x y => exact ⟨x,by simp⟩
  obtain ⟨e,⟨he,hev⟩,_⟩ := hM.2 v (Finset.mem_univ v)
  obtain ⟨f,⟨hf,hfv⟩,_⟩ := hN.2 v (Finset.mem_univ v)
  have heU : e ∈ M ∪ N := Finset.mem_union_left N he
  have heS : e ∈ S := by
    rw [← haS]
    exact (mem_componentEdges _ _ _).mpr ⟨heU, shares_reachable ha heU hav hev⟩
  by_cases hef : ends e = ends f
  · left
    refine ⟨e,he,f,hf,hef,?_⟩
    rw [← haS, componentEdges_eq (shares_reachable ha heU hav hev)]
    exact parallel_component ends hM hN he hf hef
  · right
    obtain ⟨w,hw⟩ := exists_partner ends hev
    have hadj : (discrepancy ends hloop M N).Adj v w := by
      apply (discrepancy_adj_iff ends hloop M N v w).mpr
      refine Or.inl ⟨⟨e,he,hw⟩,?_⟩
      rintro ⟨g,hg,hgw⟩
      have hgv : v ∈ ends g := by rw [hgw]; simp
      have hgf := hN.unique (Finset.mem_univ v) hg hgv hf hfv
      apply hef
      rw [hw,← hgf,hgw]
    let H := discrepancy ends hloop M N
    obtain ⟨p,hp,_,_,_⟩ := discrepancy_component_even_cycle ends hloop M N hM hN
      (H.connectedComponentMk v) v rfl ⟨w,hadj⟩
    let c := indexedCycle ends hloop M N hM hN p hp
    have hU : ∀ i, c.edgeAt i ∈ M ∪ N := by
      intro i
      exact indexedCycle_edge_mem ends hloop M N hM hN p hp (c.index i)
    have hv0 : c.vertexAt 0 = v := by
      simp [c,IndexedCycle.vertexAt,IndexedCycle.index,indexedCycle,cyclicVertex]
    have hec : e ∈ c.edgeSet :=
      c.edge_incident_cycle_mem hM hN hU heU 0 (by have := c.four_le; omega) (hv0.symm ▸ hev)
    refine ⟨c,hU,?_⟩
    exact component_eq_of_shares hS (c.edgeSet_mem_components hM hN hU) heS hec hev hev

end MatchingFPRAS.Transport.Overlay

end OAI
