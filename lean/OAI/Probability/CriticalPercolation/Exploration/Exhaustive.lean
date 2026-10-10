import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.SearchTree

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def Exhaustive (G : BondGraph V E) (order : List (Dart V E)) : Prop :=
  ∀ v e t, G.ends e = s(v,t) → (v,e,t) ∈ order

def Frontier (G : BondGraph V E) (st : State V E) (stack : List (Dart V E)) : Prop :=
  ∀ v ∈ st.reached, ∀ e t, G.ends e = s(v,t) → t ∉ st.reached →
    e ∈ st.read ∨ (v,e,t) ∈ stack

def ReadConsistent (G : BondGraph V E) (st : State V E) (ω : E → Bool) : Prop :=
  ∀ e ∈ st.read, ω e = true → ∀ v ∈ G.ends e, v ∈ st.reached

omit [DecidableEq V] [DecidableEq E] in
lemma openEdge_reachable (G : BondGraph V E) (ω : E → Bool)
    {v e t} (he : ω e = true) (heq : G.ends e = s(v,t)) :
    (G.openGraph {e | ω e = true}).Reachable v t := by
  rcases eq_or_ne v t with rfl | hne
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩)

omit [DecidableEq V] [DecidableEq E] in
lemma frontier_pop (G : BondGraph V E) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : Frontier G st ((v,e,t)::rest))
    (hskip : t ∈ st.reached ∨ e ∈ st.read ∨ v ∉ st.reached ∨ G.ends e ≠ s(v,t)) :
    Frontier G st rest := by
  intro u hu f y hfy hy
  rcases h u hu f y hfy hy with hf | hf
  · exact Or.inl hf
  · rcases List.mem_cons.mp hf with hd | hd
    · simp only [Prod.mk.injEq] at hd
      rcases hd with ⟨rfl,rfl,rfl⟩
      rcases hskip with ht | he | hv | heq
      · exact (hy ht).elim
      · exact Or.inl he
      · exact (hv hu).elim
      · exact (heq hfy).elim
    · exact Or.inr hd

omit [DecidableEq V] in
lemma frontier_closed (G : BondGraph V E) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : Frontier G st ((v,e,t)::rest)) : Frontier G (st.closed e) rest := by
  intro u hu f y hfy hy
  rcases h u hu f y hfy hy with hf | hf
  · exact Or.inl (Finset.mem_insert_of_mem hf)
  · rcases List.mem_cons.mp hf with hd | hd
    · simp only [Prod.mk.injEq] at hd
      rcases hd with ⟨rfl,rfl,rfl⟩
      exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr hd

lemma frontier_opened (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : Frontier G st ((v,e,t)::rest)) :
    Frontier G (st.opened e t) (push G order t ++ rest) := by
  intro u hu f y hfy hy
  rcases Finset.mem_insert.mp hu with rfl | hu
  · apply Or.inr
    apply List.mem_append_left
    apply List.mem_filter.mpr
    exact ⟨ho u f y hfy,by simpa only [decide_eq_true_eq, true_and] using hfy⟩
  · have hy' : y ∉ st.reached := fun hy' => hy (Finset.mem_insert_of_mem hy')
    rcases h u hu f y hfy hy' with hf | hf
    · exact Or.inl (Finset.mem_insert_of_mem hf)
    · rcases List.mem_cons.mp hf with hd | hd
      · simp only [Prod.mk.injEq] at hd
        rcases hd with ⟨rfl,rfl,rfl⟩
        exact Or.inl (Finset.mem_insert_self _ _)
      · exact Or.inr (List.mem_append_right _ hd)

omit [DecidableEq V] in
lemma readConsistent_closed (G : BondGraph V E) (st : State V E) (ω : E → Bool)
    (h : ReadConsistent G st ω) {e : E} (he : ω e = false) :
    ReadConsistent G (st.closed e) ω := by
  intro f hf hfopen v hv
  rcases Finset.mem_insert.mp hf with rfl | hf
  · simp [he] at hfopen
  · exact h f hf hfopen v hv

lemma readConsistent_opened (G : BondGraph V E) (st : State V E) (ω : E → Bool)
    (h : ReadConsistent G st ω) {v e t} (hv : v ∈ st.reached) (heq : G.ends e = s(v,t)) :
    ReadConsistent G (st.opened e t) ω := by
  intro f hf hfopen u hu
  rcases Finset.mem_insert.mp hf with rfl | hf
  · have hu' : u = v ∨ u = t := by simpa only [heq,Sym2.mem_iff] using hu
    rcases hu' with rfl | rfl
    · exact Finset.mem_insert_of_mem hv
    · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (h f hf hfopen u hu)

omit [DecidableEq V] [DecidableEq E] in
lemma empty_frontier_closed (G : BondGraph V E) (st : State V E) (ω : E → Bool)
    (hf : Frontier G st []) (hc : ReadConsistent G st ω) :
    ∀ v ∈ st.reached, ∀ t, (G.openGraph {e | ω e = true}).Adj v t → t ∈ st.reached := by
  intro v hv t ht
  obtain ⟨⟨e,he,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp ht
  by_contra htr
  rcases hf v hv e t heq htr with hr | hr
  · exact htr (hc e hr he t (by simp [heq]))
  · simp at hr

variable [Fintype V]

theorem compile_success_or_closed (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (B : Set V) (fuel : ℕ) (st : State V E)
    (stack : List (Dart V E)) (ω : E → Bool)
    (hf : Frontier G st stack) (hc : ReadConsistent G st ω) (hr : rank order st stack ≤ fuel) :
    let final := (compile G order B fuel st stack).run ω
    (∃ v ∈ final.reached, v ∈ B) ∨
      (∀ v ∈ final.reached, ∀ t, (G.openGraph {e | ω e = true}).Adj v t → t ∈ final.reached) := by
  induction fuel generalizing st stack with
  | zero =>
    have hs : stack = [] := by
      have hh : stack.length = 0 := by dsimp [rank] at hr; omega
      exact List.length_eq_zero_iff.mp hh
    subst stack
    exact Or.inr (empty_frontier_closed G st ω hf hc)
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact Or.inl hh
    · cases stack with
      | nil => exact Or.inr (empty_frontier_closed G st ω hf hc)
      | cons d rest =>
        rcases d with ⟨v,e,t⟩
        dsimp only
        split_ifs with hd
        · exact ih st rest (frontier_pop G st v e t rest hf hd) hc
            (by have hh := rank_pop order st (v,e,t) rest; omega)
        · have hdec : t ∉ st.reached ∧ e ∉ st.read ∧ v ∈ st.reached ∧ G.ends e = s(v,t) := by
            push Not at hd
            exact hd
          rw [SearchTree.run]
          split_ifs with he
          · exact ih _ _ (frontier_opened G order ho st v e t rest hf)
              (readConsistent_opened G st ω hc hdec.2.2.1 hdec.2.2.2)
              (by have hh := rank_opened G order st (v,e,t) rest hdec.1; dsimp only at hh; omega)
          · have he' : ω e = false := Bool.eq_false_iff.mpr he
            exact ih _ _ (frontier_closed G st v e t rest hf)
              (readConsistent_closed G st ω hc he')
              (by have hh := rank_closed order st (v,e,t) rest; dsimp only at hh; omega)

end CriticalPercolation.LazyDFS

end
end

end OAI
