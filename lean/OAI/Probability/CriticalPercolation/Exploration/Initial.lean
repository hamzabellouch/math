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

lemma compile_sound (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E)) (ω : E → Bool) (w : V)
    (hs : ∀ v ∈ st.reached, (G.openGraph {e | ω e = true}).Reachable w v) :
    ∀ v ∈ ((compile G order B fuel st stack).run ω).reached,
      (G.openGraph {e | ω e = true}).Reachable w v := by
  induction fuel generalizing st stack with
  | zero => exact hs
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact hs
    · cases stack with
      | nil => exact hs
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest hs
        · rw [SearchTree.run]
          split_ifs with he
          · apply ih
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · have hdec : d.2.2 ∉ st.reached ∧ d.2.1 ∉ st.read ∧ d.1 ∈ st.reached ∧
                  G.ends d.2.1 = s(d.1,d.2.2) := by
                push Not at hd
                exact hd
              exact (hs d.1 hdec.2.2.1).trans (openEdge_reachable G ω he hdec.2.2.2)
            · exact hs u hu
          · exact ih (st.closed d.2.1) rest hs

omit [DecidableEq V] [DecidableEq E] in
lemma reachable_mem_of_closed (H : SimpleGraph V) (S : Finset V)
    (hc : ∀ v ∈ S, ∀ t, H.Adj v t → t ∈ S) {v t : V}
    (hr : H.Reachable v t) (hv : v ∈ S) : t ∈ S := by
  have hh : ∀ {u z : V}, H.Walk u z → u ∈ S → z ∈ S := by
    intro u z path
    induction path with
    | nil => exact id
    | cons ha _ ih => exact fun hu => ih (hc _ hu _ ha)
  exact hr.elim (fun path => hh path hv)

noncomputable def initial (w : V) : State V E := ⟨{w},∅⟩

omit [DecidableEq E] in
lemma initial_frontier (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (w : V) : Frontier G (initial w) (push G order w) := by
  intro v hv e t he _
  have hvw : v = w := Finset.mem_singleton.mp hv
  subst v
  exact Or.inr (List.mem_filter.mpr ⟨ho w e t he,by simpa only [decide_eq_true_eq,true_and] using he⟩)

omit [DecidableEq V] [DecidableEq E] in
lemma initial_consistent (G : BondGraph V E) (w : V) (ω : E → Bool) :
    ReadConsistent G (initial w) ω := by
  intro e he
  exact (Finset.notMem_empty e he).elim

variable [Fintype V]

noncomputable def search (G : BondGraph V E) (order : List (Dart V E)) (w : V) (B : Set V) :
    SearchTree E (State V E) :=
  compile G order B (rank order (initial w) (push G order w)) (initial w) (push G order w)

theorem search_decides (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (w : V) (B : Set V) (ω : E → Bool) :
    (∃ v ∈ ((search G order w B).run ω).reached, v ∈ B) ↔
      ∃ v ∈ B, (G.openGraph {e | ω e = true}).Reachable w v := by
  have hs : ∀ v ∈ (initial (E := E) w).reached,
      (G.openGraph {e | ω e = true}).Reachable w v := by
    intro v hv
    have : v = w := Finset.mem_singleton.mp hv
    subst v
    exact .refl _
  constructor
  · rintro ⟨v,hv,hB⟩
    exact ⟨v,hB,compile_sound G order B _ _ _ ω w hs v hv⟩
  · rintro ⟨v,hB,hr⟩
    rcases compile_success_or_closed G order ho B _ (initial w) (push G order w) ω
      (initial_frontier G order ho w) (initial_consistent G w ω) le_rfl with h | h
    · exact h
    · have hw : w ∈ ((search G order w B).run ω).reached :=
        (compile_mono G order B _ (initial w) (push G order w) ω).1 (Finset.mem_singleton_self _)
      exact ⟨v,reachable_mem_of_closed _ _ h hr hw,hB⟩

theorem search_reads_nodup (G : BondGraph V E) (order : List (Dart V E))
    (w : V) (B : Set V) (ω : E → Bool) : ((search G order w B).reads ω).Nodup :=
  SearchTree.reads_nodup _ _ (compile_valid G order B _ _ _) ω

end CriticalPercolation.LazyDFS

end
end

end OAI
