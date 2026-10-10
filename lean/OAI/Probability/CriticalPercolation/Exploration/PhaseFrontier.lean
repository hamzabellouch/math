import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Exhaustive

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

def PhaseFrontier (G : BondGraph V E) (A : Set V) (st : State V E)
    (stack : List (Dart V E)) : Prop :=
  ∀ v ∈ st.reached, v ∉ A → ∀ e t, G.ends e = s(v,t) → t ∉ st.reached →
    e ∈ st.read ∨ (v,e,t) ∈ stack

omit [DecidableEq V] [DecidableEq E] in
lemma phaseFrontier_pop (G : BondGraph V E) (A : Set V) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : PhaseFrontier G A st ((v,e,t)::rest))
    (hskip : t ∈ st.reached ∨ e ∈ st.read ∨ v ∉ st.reached ∨ G.ends e ≠ s(v,t)) :
    PhaseFrontier G A st rest := by
  intro u hu huA f y hfy hy
  rcases h u hu huA f y hfy hy with hf | hf
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
lemma phaseFrontier_closed (G : BondGraph V E) (A : Set V) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : PhaseFrontier G A st ((v,e,t)::rest)) : PhaseFrontier G A (st.closed e) rest := by
  intro u hu huA f y hfy hy
  rcases h u hu huA f y hfy hy with hf | hf
  · exact Or.inl (Finset.mem_insert_of_mem hf)
  · rcases List.mem_cons.mp hf with hd | hd
    · simp only [Prod.mk.injEq] at hd
      rcases hd with ⟨rfl,rfl,rfl⟩
      exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr hd

lemma phaseFrontier_opened (G : BondGraph V E) (A : Set V) (order : List (Dart V E))
    (ho : Exhaustive G order) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : PhaseFrontier G A st ((v,e,t)::rest)) :
    PhaseFrontier G A (st.opened e t) (push G order t ++ rest) := by
  intro u hu huA f y hfy hy
  rcases Finset.mem_insert.mp hu with rfl | hu
  · exact Or.inr (List.mem_append_left _ (List.mem_filter.mpr
      ⟨ho u f y hfy,by simpa only [decide_eq_true_eq,true_and] using hfy⟩))
  · have hy' : y ∉ st.reached := fun hy' => hy (Finset.mem_insert_of_mem hy')
    rcases h u hu huA f y hfy hy' with hf | hf
    · exact Or.inl (Finset.mem_insert_of_mem hf)
    · rcases List.mem_cons.mp hf with hd | hd
      · simp only [Prod.mk.injEq] at hd
        rcases hd with ⟨rfl,rfl,rfl⟩
        exact Or.inl (Finset.mem_insert_self _ _)
      · exact Or.inr (List.mem_append_right _ hd)

omit [DecidableEq V] [DecidableEq E] in
lemma empty_phaseFrontier_closed (G : BondGraph V E) (A : Set V) (st : State V E)
    (ω : E → Bool) (hf : PhaseFrontier G A st []) (hc : ReadConsistent G st ω) :
    ∀ v ∈ st.reached, v ∉ A → ∀ t, (G.openGraph {e | ω e = true}).Adj v t →
      t ∈ st.reached := by
  intro v hv hvA t ht
  obtain ⟨⟨e,he,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp ht
  by_contra htr
  rcases hf v hv hvA e t heq htr with hr | hr
  · exact htr (hc e hr he t (by simp [heq]))
  · simp at hr

variable [Fintype V]

theorem phase_success_or_closed (G : BondGraph V E) (A : Set V) (order : List (Dart V E))
    (ho : Exhaustive G order) (B : Set V) (fuel : ℕ) (st : State V E)
    (stack : List (Dart V E)) (ω : E → Bool)
    (hf : PhaseFrontier G A st stack) (hc : ReadConsistent G st ω) (hr : rank order st stack ≤ fuel) :
    let final := (compile G order B fuel st stack).run ω
    (∃ v ∈ final.reached, v ∈ B) ∨
      (∀ v ∈ final.reached, v ∉ A → ∀ t, (G.openGraph {e | ω e = true}).Adj v t →
        t ∈ final.reached) := by
  induction fuel generalizing st stack with
  | zero =>
    have hs : stack = [] := by
      have hh : stack.length = 0 := by dsimp [rank] at hr; omega
      exact List.length_eq_zero_iff.mp hh
    subst stack
    exact Or.inr (empty_phaseFrontier_closed G A st ω hf hc)
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact Or.inl hh
    · cases stack with
      | nil => exact Or.inr (empty_phaseFrontier_closed G A st ω hf hc)
      | cons d rest =>
        rcases d with ⟨v,e,t⟩
        dsimp only
        split_ifs with hd
        · exact ih st rest (phaseFrontier_pop G A st v e t rest hf hd) hc
            (by have hh := rank_pop order st (v,e,t) rest; omega)
        · have hdec : t ∉ st.reached ∧ e ∉ st.read ∧ v ∈ st.reached ∧ G.ends e = s(v,t) := by
            push Not at hd
            exact hd
          rw [SearchTree.run]
          split_ifs with he
          · exact ih _ _ (phaseFrontier_opened G A order ho st v e t rest hf)
              (readConsistent_opened G st ω hc hdec.2.2.1 hdec.2.2.2)
              (by have hh := rank_opened G order st (v,e,t) rest hdec.1; dsimp only at hh; omega)
          · have he' : ω e = false := Bool.eq_false_iff.mpr he
            exact ih _ _ (phaseFrontier_closed G A st v e t rest hf)
              (readConsistent_closed G st ω hc he')
              (by have hh := rank_closed order st (v,e,t) rest; dsimp only at hh; omega)

omit [Fintype V] in

theorem compile_append_of_success (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (young older : List (Dart V E)) (ω : E → Bool)
    (hs : ∃ v ∈ ((compile G order B fuel st young).run ω).reached, v ∈ B) :
    (compile G order B fuel st (young++older)).run ω = (compile G order B fuel st young).run ω ∧
    (compile G order B fuel st (young++older)).reads ω = (compile G order B fuel st young).reads ω := by
  induction fuel generalizing st young with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [compile.eq_def G order B (n+1) st] at hs ⊢
    by_cases hh : ∃ v ∈ st.reached, v ∈ B
    · simp [hh,SearchTree.run,SearchTree.reads]
    · simp only [hh,↓reduceIte] at hs ⊢
      cases young with
      | nil => exact (hh hs).elim
      | cons d rest =>
        simp only [List.cons_append]
        dsimp only at hs ⊢
        by_cases hd : d.2.2 ∈ st.reached ∨ d.2.1 ∈ st.read ∨ d.1 ∉ st.reached ∨
            G.ends d.2.1 ≠ s(d.1,d.2.2)
        · simp only [hd,↓reduceIte] at hs ⊢
          exact ih st rest hs
        · simp only [hd,↓reduceIte,SearchTree.run,SearchTree.reads] at hs ⊢
          by_cases he : ω d.2.1 = true
          · simp only [he,↓reduceIte] at hs ⊢
            have h := ih (st.opened d.2.1 d.2.2) (push G order d.2.2++rest) hs
            simpa only [List.append_assoc,List.cons.injEq,true_and] using h
          · simp only [he,Bool.false_eq_true,↓reduceIte] at hs ⊢
            have h := ih (st.closed d.2.1) rest hs
            simpa only [List.cons.injEq,true_and] using h

end CriticalPercolation.LazyDFS

end
end

end OAI
