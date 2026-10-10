import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Select

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.MarkedTree
open QueryTree

variable {E A : Type*}

lemma sum_visited_nodes (t : MarkedTree E A) (ω : E → Bool) (f : E → A → ℝ) :
    (∑ n : t.bare.Node, if t.bare.visits n ω then f (t.bare.bit n) (t.nodeLabel n) else 0) =
      ((t.trace ω).map (fun x => f x.1 x.2)).sum := by
  induction t with
  | stop =>
    change (∑ n : PEmpty, _) = 0
    simp
  | ask e a l r hl hr =>
    change (∑ n : PUnit ⊕ (l.bare.Node ⊕ r.bare.Node), _) = _
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    cases h : ω e
    · simp only [Fintype.sum_unique, bare, QueryTree.visits, QueryTree.response, QueryTree.run,
        h, Bool.false_eq_true, ↓reduceIte, Option.isSome_some, QueryTree.bit,
        nodeLabel, Option.isSome_none, Finset.sum_const_zero, add_zero, trace, List.map_cons,
        List.sum_cons]
      congr 1
    · simp only [Fintype.sum_unique, bare, QueryTree.visits, QueryTree.response, QueryTree.run,
        h, ↓reduceIte, Option.isSome_some, QueryTree.bit,
        nodeLabel, Option.isSome_none, Bool.false_eq_true, Finset.sum_const_zero, zero_add,
        trace, List.map_cons, List.sum_cons]
      congr 1

def Tagged (coord : A → E) : MarkedTree E A → Prop
  | .stop => True
  | .ask e a l r => e = coord a ∧ l.Tagged coord ∧ r.Tagged coord

lemma tagged_bit (coord : A → E) (t : MarkedTree E A) (ht : t.Tagged coord)
    (n : t.bare.Node) : t.bare.bit n = coord (t.nodeLabel n) := by
  induction t with
  | stop => exact PEmpty.elim n
  | ask e a l r hl hr =>
    rcases n with _ | (n | n)
    · exact ht.1
    · exact hl ht.2.1 n
    · exact hr ht.2.2 n

lemma tagged_map {B : Type*} (coord : B → E) (f : A → B) (t : MarkedTree E A)
    (ht : t.Tagged (coord ∘ f)) : (t.map f).Tagged coord := by
  induction t with
  | stop => trivial
  | ask e a l r hl hr => exact ⟨ht.1, hl ht.2.1, hr ht.2.2⟩

lemma tagged_append (coord : A → E) (t s : MarkedTree E A)
    (ht : t.Tagged coord) (hs : s.Tagged coord) : (t.append s).Tagged coord := by
  induction t with
  | stop => exact hs
  | ask e a l r hl hr => exact ⟨ht.1, hl ht.2.1, hr ht.2.2⟩

lemma tagged_sequence (coord : A → E) (ts : List (MarkedTree E A))
    (ht : ∀ t ∈ ts, t.Tagged coord) : (sequence ts).Tagged coord := by
  induction ts with
  | nil => trivial
  | cons t ts ih =>
    apply tagged_append
    · exact ht t (by simp)
    · exact ih (fun s hs => ht s (List.mem_cons_of_mem _ hs))

variable [DecidableEq E]
lemma tagged_cached (coord : A → E) (t : MarkedTree E A)
    (ht : t.Tagged coord) (σ : Cache E) : (t.cached σ).Tagged coord := by
  induction t generalizing σ with
  | stop => trivial
  | ask e a l r hl hr =>
    cases hs : σ e with
    | none =>
      simp only [cached, hs, Tagged]
      exact ⟨ht.1, hl ht.2.1 _, hr ht.2.2 _⟩
    | some b =>
      cases b
      · simpa only [cached, hs] using hl ht.2.1 σ
      · simpa only [cached, hs] using hr ht.2.2 σ

lemma mem_select_block (S : Finset E) (pre mid post : List (E × A)) (x : E × A)
    (hp : x ∉ pre) (hs : x ∉ post) (hm : (mid.map Prod.fst).Nodup) :
    x ∈ select S (pre ++ mid ++ post) ↔ x ∈ mid ∧ x.1 ∉ S ∪ (pre.map Prod.fst).toFinset := by
  rw [List.append_assoc, select_append, select_append]
  have hp' : x ∉ select S pre := fun h => hp (mem_select S pre x h)
  have hs' (U : Finset E) : x ∉ select U post := fun h => hs (mem_select U post x h)
  simp only [List.mem_append, hp', hs', false_or, or_false]
  rw [select_of_nodup _ _ hm]
  simp

end CriticalPercolation.MarkedTree

namespace CriticalPercolation.QueryTree
variable {E : Type*}
lemma tagged_marked (t : QueryTree E) : t.marked.Tagged t.bit := by
  induction t with
  | stop => trivial
  | ask e l r hl hr =>
    refine ⟨rfl, ?_, ?_⟩
    · apply MarkedTree.tagged_map
      exact hl
    · apply MarkedTree.tagged_map
      exact hr
end CriticalPercolation.QueryTree

end
end

end OAI
