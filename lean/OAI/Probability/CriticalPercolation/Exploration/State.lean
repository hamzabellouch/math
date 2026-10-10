import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.SearchTree

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

structure State (V E : Type*) where
  reached : Finset V
  read : Finset E

noncomputable def eligible (G : BondGraph V E) (st : State V E) (e : E) : Prop :=
  e ∉ st.read ∧ ∃ v ∈ st.reached, v ∈ G.ends e

noncomputable def closed (st : State V E) (e : E) : State V E :=
  ⟨st.reached, insert e st.read⟩

noncomputable def opened (G : BondGraph V E) (st : State V E) (e : E) : State V E :=
  ⟨st.reached ∪ (G.ends e).toFinset, insert e st.read⟩

noncomputable def compile (G : BondGraph V E) : ℕ → State V E → SearchTree E (State V E)
  | 0, st => .done st
  | n+1, st => if h : ∃ e, eligible G st e then
      let e := Classical.choose h
      .ask e (compile G n (closed st e)) (compile G n (opened G st e))
    else .done st

omit [DecidableEq V] [DecidableEq E] in
lemma eligible_succ (G : BondGraph V E) (st : State V E) (h : ∃ e, eligible G st e) :
    eligible G st (Classical.choose h) := Classical.choose_spec h

lemma compile_valid (G : BondGraph V E) (n : ℕ) (st : State V E) :
    (compile G n st).Valid st.read := by
  induction n generalizing st with
  | zero => trivial
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · exact ⟨(eligible_succ G st h).1, ih _, ih _⟩
    · trivial

omit [DecidableEq V] [DecidableEq E] in
lemma edge_reachable (G : BondGraph V E) (ω : E → Bool) {e : E} (he : ω e = true)
    {v t : V} (hv : v ∈ G.ends e) (ht : t ∈ G.ends e) :
    (G.openGraph {e | ω e = true}).Reachable v t := by
  rcases eq_or_ne v t with rfl | hne
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e,he,(Sym2.mem_and_mem_iff hne).mp ⟨hv,ht⟩⟩,hne⟩)

def Consistent (G : BondGraph V E) (st : State V E) (ω : E → Bool) : Prop :=
  ∀ e ∈ st.read, ω e = true → ∀ v ∈ G.ends e, v ∈ st.reached

def Sound (G : BondGraph V E) (S : Set V) (st : State V E) (ω : E → Bool) : Prop :=
  ∀ v ∈ st.reached, ∃ s ∈ S, (G.openGraph {e | ω e = true}).Reachable s v

omit [DecidableEq V] in
lemma consistent_closed (G : BondGraph V E) (st : State V E) (ω : E → Bool) (e : E)
    (h : Consistent G st ω) (he : ω e ≠ true) : Consistent G (closed st e) ω := by
  intro f hf hw v hv
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact (he hw).elim
  · exact h f hf hw v hv

lemma consistent_opened (G : BondGraph V E) (st : State V E) (ω : E → Bool) (e : E)
    (h : Consistent G st ω) : Consistent G (opened G st e) ω := by
  intro f hf hw v hv
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact Finset.mem_union_right _ (Sym2.mem_toFinset.mpr hv)
  · exact Finset.mem_union_left _ (h f hf hw v hv)

lemma sound_opened (G : BondGraph V E) (S : Set V) (st : State V E) (ω : E → Bool) (e : E)
    (h : Sound G S st ω) (hel : eligible G st e) (he : ω e = true) :
    Sound G S (opened G st e) ω := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact h v hv
  · obtain ⟨u,hu,hue⟩ := hel.2
    obtain ⟨s,hs,hsu⟩ := h u hu
    exact ⟨s,hs,hsu.trans (edge_reachable G ω he hue (Sym2.mem_toFinset.mp hv))⟩

lemma compile_invariants (G : BondGraph V E) (S : Set V) (n : ℕ) (st : State V E)
    (ω : E → Bool) (hc : Consistent G st ω) (hs : Sound G S st ω) :
    Consistent G ((compile G n st).run ω) ω ∧
      Sound G S ((compile G n st).run ω) ω ∧
      st.reached ⊆ ((compile G n st).run ω).reached := by
  induction n generalizing st with
  | zero => exact ⟨hc,hs,Finset.Subset.refl _⟩
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      rw [SearchTree.run]
      split_ifs with he
      · obtain ⟨hc',hs',hm⟩ := ih (opened G st (Classical.choose h))
          (consistent_opened G st ω _ hc)
          (sound_opened G S st ω _ hs (eligible_succ G st h) he)
        exact ⟨hc',hs',Finset.Subset.trans Finset.subset_union_left hm⟩
      · exact ih (closed st (Classical.choose h)) (consistent_closed G st ω _ hc he) hs
    · exact ⟨hc,hs,Finset.Subset.refl _⟩

lemma compile_read (G : BondGraph V E) (n : ℕ) (st : State V E) (ω : E → Bool) :
    ((compile G n st).run ω).read = st.read ∪ ((compile G n st).reads ω).toFinset := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.reads]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      rw [SearchTree.run,SearchTree.reads]
      split_ifs with he
      · rw [ih]
        simp only [opened,List.toFinset_cons]
        simp only [Finset.insert_union,Finset.union_insert]
      · rw [ih]
        simp only [closed,List.toFinset_cons]
        simp only [Finset.insert_union,Finset.union_insert]
    · simp [SearchTree.run,SearchTree.reads]

variable [Fintype E]

lemma compile_exhausted (G : BondGraph V E) (n : ℕ) (st : State V E) (ω : E → Bool)
    (hbudget : Fintype.card E ≤ n + st.read.card) :
    ¬∃ e, eligible G ((compile G n st).run ω) e := by
  induction n generalizing st with
  | zero =>
    rintro ⟨e,he,_⟩
    have hec := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ st.read,fun h => he (h ▸ Finset.mem_univ e)⟩)
    simp only [Finset.card_univ] at hec
    omega
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      have he := (eligible_succ G st h).1
      have hc : Fintype.card E ≤ n + (insert (Classical.choose h) st.read).card := by
        rw [Finset.card_insert_of_notMem he]
        omega
      rw [SearchTree.run]
      split_ifs
      · exact ih _ hc
      · exact ih _ hc
    · exact h

lemma compile_reads_incident (G : BondGraph V E) (n : ℕ) (st : State V E) (ω : E → Bool)
    (hc : Consistent G st ω) (hs : Sound G Set.univ st ω) :
    ∀ e ∈ (compile G n st).reads ω,
      ∃ v ∈ ((compile G n st).run ω).reached, v ∈ G.ends e := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.reads]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      rw [SearchTree.reads,SearchTree.run]
      by_cases he : ω (Classical.choose h) = true
      · simp only [he,↓reduceIte,List.mem_cons]
        intro e hem
        rcases hem with rfl | hem
        · obtain ⟨v,hv,hve⟩ := (eligible_succ G st h).2
          have hm := (compile_invariants G Set.univ n (opened G st (Classical.choose h)) ω
            (consistent_opened G st ω _ hc)
            (sound_opened G Set.univ st ω _ hs (eligible_succ G st h) he)).2.2
          exact ⟨v,hm (Finset.mem_union_left _ hv),hve⟩
        · exact ih _ (consistent_opened G st ω _ hc)
            (sound_opened G Set.univ st ω _ hs (eligible_succ G st h) he) e hem
      · simp only [he,List.mem_cons]
        intro e hem
        rcases hem with rfl | hem
        · obtain ⟨v,hv,hve⟩ := (eligible_succ G st h).2
          have hm := (compile_invariants G Set.univ n (closed st (Classical.choose h)) ω
            (consistent_closed G st ω _ hc he) hs).2.2
          exact ⟨v,hm hv,hve⟩
        · exact ih _ (consistent_closed G st ω _ hc he) hs e hem
    · simp [SearchTree.reads]

end CriticalPercolation.ExactExposure

end
end

end OAI
