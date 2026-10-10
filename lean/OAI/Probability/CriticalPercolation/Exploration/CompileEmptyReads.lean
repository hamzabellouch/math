import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.TargetSearch

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree BondGraph

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

lemma compile_empty_reads (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (ω : E → Bool) :
    (compile G order B fuel st []).reads ω = [] := by
  cases fuel with
  | zero => rfl
  | succ n =>
    rw [compile.eq_def]
    dsimp only
    split_ifs <;> rfl

variable [Fintype V]

theorem compile_reads_rank_independent (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel fuel' : ℕ) (st : State V E) (stack : List (Dart V E)) (ω : E → Bool)
    (hr : rank order st stack ≤ fuel) (hr' : rank order st stack ≤ fuel') :
    (compile G order B fuel st stack).reads ω = (compile G order B fuel' st stack).reads ω := by
  induction fuel generalizing fuel' st stack with
  | zero =>
    have hnil : stack = [] := by
      have : stack.length = 0 := by unfold rank at hr; omega
      exact List.length_eq_zero_iff.mp this
    subst stack
    rw [compile_empty_reads,compile_empty_reads]
  | succ n ih =>
    cases fuel' with
    | zero =>
      have hnil : stack = [] := by
        have : stack.length = 0 := by unfold rank at hr'; omega
        exact List.length_eq_zero_iff.mp this
      subst stack
      rw [compile_empty_reads,compile_empty_reads]
    | succ m =>
      rw [compile.eq_def,compile.eq_def]
      dsimp only
      split_ifs with hh
      · rfl
      · cases stack with
        | nil => rfl
        | cons d rest =>
          dsimp only
          split_ifs with hd
          · have hpop := rank_pop order st d rest
            exact ih m st rest (by omega) (by omega)
          · rw [reads,reads]
            congr 1
            split_ifs with hω
            · have hopen := rank_opened G order st d rest (fun h => hd (Or.inl h))
              exact ih m _ _ (by omega) (by omega)
            · have hclosed := rank_closed order st d rest
              exact ih m _ _ (by omega) (by omega)

omit [Fintype V] [DecidableEq E] in
lemma push_goodDarts (G : BondGraph V E) (order : List (Dart V E)) (v : V) :
    GoodDarts G (push G order v) := by
  intro d hd
  have hh := (List.mem_filter.mp hd).2
  exact (of_decide_eq_true hh).2

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma goodDarts_append (G : BondGraph V E) (l r : List (Dart V E))
    (hl : GoodDarts G l) (hr : GoodDarts G r) : GoodDarts G (l++r) := by
  intro d hd
  exact (List.mem_append.mp hd).elim (hl d) (hr d)

omit [Fintype V] in

theorem compile_reads_targetWiring (G : BondGraph V E) (B : Set V)
    (order : List (Dart V E)) (horder : GoodDarts G order) (fuel : ℕ)
    (st : State V E) (stack : List (Dart V E)) (hs : GoodDarts G stack)
    (ω : E → Bool) :
    (compile G order B fuel st stack).reads ω =
      (compile (G.wireTargets B) (order.map (mapDart B)) {none} fuel (mapState B st)
        (stack.map (mapDart B))).reads ω := by
  induction fuel generalizing st stack with
  | zero => rfl
  | succ n ih =>
    rw [compile.eq_def,compile.eq_def]
    dsimp only
    simp only [target_hit_map]
    split_ifs with hh
    · rfl
    · cases stack with
      | nil => rfl
      | cons d rest =>
        have hd := hs d (List.mem_cons_self ..)
        have hd' := mapDart_ends G B d hd
        have hr : GoodDarts G rest := fun d h => hs d (List.mem_cons_of_mem _ h)
        simp only [List.map_cons]
        have hmem := mapState_mem B st hh
        have hRead : (mapState B st).read = st.read := rfl
        have hEnds : (G.wireTargets B).ends d.2.1 =
            s(collapseTarget B d.1, collapseTarget B d.2.2) := hd'
        simp only [mapDart, hRead, hEnds, hd, ne_eq, not_true_eq_false, or_false, hmem]
        split_ifs with hbad
        · exact ih st rest hr
        · rw [reads,reads]
          congr 1
          split_ifs with hbit
          · by_cases hzB : d.2.2 ∈ B
            · have hstop := compile_stop G order B n (st.opened d.2.1 d.2.2)
                (push G order d.2.2++rest) ⟨d.2.2,Finset.mem_insert_self _ _,hzB⟩
              have hzNone := (collapseTarget_eq_none B d.2.2).mpr hzB
              have hstop' := compile_stop (G.wireTargets B) (order.map (mapDart B)) {none} n
                ((mapState B st).opened d.2.1 (collapseTarget B d.2.2))
                (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B d.2.2) ++
                  rest.map (mapDart B))
                ⟨none,by simp [State.opened,hzNone],Set.mem_singleton none⟩
              rw [hstop,hstop']; rfl
            · have hnew := ih (st.opened d.2.1 d.2.2) (push G order d.2.2++rest)
                (goodDarts_append G _ _ (push_goodDarts G order d.2.2) hr)
              rw [mapState_opened,List.map_append,push_mapTarget G B order horder d.2.2 hzB] at hnew
              exact hnew
          · exact ih (st.closed d.2.1) rest hr

end CriticalPercolation.LazyDFS

end
end

end OAI
