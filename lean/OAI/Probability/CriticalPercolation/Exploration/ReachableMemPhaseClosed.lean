import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.PhaseFrontier

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

omit [DecidableEq V] [DecidableEq E] in
lemma reachable_mem_of_phase_closed (H : SimpleGraph V) (A : Set V) (S : Finset V)
    (hc : ∀ v ∈ S, v ∉ A → ∀ t, H.Adj v t → t ∈ S) {z t : V}
    (ha : ∀ a ∈ A, ¬H.Reachable z a) (ht : H.Reachable z t) (hz : z ∈ S) : t ∈ S := by
  have hh : ∀ {u v : V}, H.Walk u v → H.Reachable z u → u ∈ S → v ∈ S := by
    intro u v path
    induction path with
    | nil => exact fun _ h => h
    | @cons u v y h path ih =>
      intro hzu hu
      exact ih (hzu.trans h.reachable) (hc u hu (fun hA => ha u hA hzu) v h)
  exact ht.elim (fun path => hh path (.refl _) hz)

lemma opened_phaseFrontier (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (st : State V E) (f : E) (z : V) :
    PhaseFrontier G (st.reached : Set V) (st.opened f z) (push G order z) := by
  intro v hv hvA e t het _
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact Or.inr (List.mem_filter.mpr
      ⟨ho v e t het,by simpa only [decide_eq_true_eq,true_and] using het⟩)
  · exact (hvA hv).elim

variable [Fintype V]

theorem phase_hits_of_avoiding_connection (G : BondGraph V E) (A : Set V)
    (order : List (Dart V E)) (ho : Exhaustive G order) (B : Set V)
    (fuel : ℕ) (st : State V E) (young : List (Dart V E)) (ω : E → Bool)
    (hf : PhaseFrontier G A st young) (hc : ReadConsistent G st ω)
    (hr : rank order st young ≤ fuel) (H : SimpleGraph V)
    (hH : H ≤ G.openGraph {e | ω e = true}) (z : V) (hz : z ∈ st.reached)
    (ha : ∀ a ∈ A, ¬H.Reachable z a) (ht : ∃ t ∈ B, H.Reachable z t) :
    ∃ t ∈ ((compile G order B fuel st young).run ω).reached, t ∈ B := by
  rcases phase_success_or_closed G A order ho B fuel st young ω hf hc hr with h | h
  · exact h
  · obtain ⟨t,htB,hzt⟩ := ht
    have hclosed : ∀ v ∈ ((compile G order B fuel st young).run ω).reached,
        v ∉ A → ∀ u, H.Adj v u → u ∈ ((compile G order B fuel st young).run ω).reached := by
      intro v hv hvA u hvu
      exact h v hv hvA u (hH hvu)
    exact ⟨t,reachable_mem_of_phase_closed H A _ hclosed ha hzt
      ((compile_mono G order B fuel st young ω).1 hz),htB⟩

theorem phase_no_older_reads (G : BondGraph V E) (A : Set V)
    (order : List (Dart V E)) (ho : Exhaustive G order) (B : Set V)
    (fuel : ℕ) (st : State V E) (young older : List (Dart V E)) (ω : E → Bool)
    (hf : PhaseFrontier G A st young) (hc : ReadConsistent G st ω)
    (hr : rank order st young ≤ fuel) (H : SimpleGraph V)
    (hH : H ≤ G.openGraph {e | ω e = true}) (z : V) (hz : z ∈ st.reached)
    (ha : ∀ a ∈ A, ¬H.Reachable z a) (ht : ∃ t ∈ B, H.Reachable z t) :
    (compile G order B fuel st (young++older)).reads ω =
      (compile G order B fuel st young).reads ω :=
  (compile_append_of_success G order B fuel st young older ω
    (phase_hits_of_avoiding_connection G A order ho B fuel st young ω hf hc hr H hH z hz ha ht)).2

end CriticalPercolation.LazyDFS

end
end

end OAI
