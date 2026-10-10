import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Visits

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
variable {E A : Type*} [DecidableEq E] [Fintype E]

def select : Finset E → List (E × A) → List (E × A)
  | _, [] => []
  | S, x :: xs =>
      if x.1 ∈ S then select S xs else x :: select (insert x.1 S) xs

lemma fresh_eq_select (ω : E → Bool) (σ : Cache E) (xs : List (E × A)) :
    fresh ω σ xs = select (domain σ) xs := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih =>
    simp only [fresh, select, ih, domain_update]
    cases hs : σ x.1 with
    | none => simp [mem_domain, hs]
    | some b =>
      have hm : x.1 ∈ domain σ := by simp [mem_domain, hs]
      simp [hm, Finset.insert_eq_of_mem hm]

lemma trace_cached_select (t : MarkedTree E A) (σ : Cache E) (ω : E → Bool)
    (hσ : Compatible σ ω) :
    (t.cached σ).trace ω = select (domain σ) (t.trace ω) := by
  rw [trace_cached t σ ω hσ, fresh_eq_select]

omit [Fintype E] in
lemma mem_select (S : Finset E) (xs : List (E × A)) (x : E × A) :
    x ∈ select S xs → x ∈ xs := by
  induction xs generalizing S with
  | nil => simp [select]
  | cons y ys ih =>
    simp only [select]
    split_ifs with h
    · exact fun hm => List.mem_cons_of_mem _ (ih S hm)
    · intro hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ hm)

omit [Fintype E] in
lemma select_append (S : Finset E) (xs ys : List (E × A)) :
    select S (xs ++ ys) = select S xs ++ select (S ∪ (xs.map Prod.fst).toFinset) ys := by
  induction xs generalizing S with
  | nil => simp [select]
  | cons x xs ih =>
    simp only [List.cons_append, select]
    by_cases hx : x.1 ∈ S
    · simp only [hx, ↓reduceIte, ih, List.map_cons, List.toFinset_cons]
      congr 2
      ext e
      simp only [Finset.mem_union, Finset.mem_insert]
      aesop
    · simp only [hx, ↓reduceIte, ih, List.cons_append, List.map_cons, List.toFinset_cons]
      congr 3
      ext e
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto

omit [Fintype E] in
lemma select_of_nodup (S : Finset E) (xs : List (E × A))
    (hn : (xs.map Prod.fst).Nodup) :
    select S xs = xs.filter (fun x => x.1 ∉ S) := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [select, List.filter_cons]
    by_cases hx : x.1 ∈ S
    · simp [hx, ih _ hn.2]
    · simp only [hx, ↓reduceIte, ih _ hn.2]
      congr 1
      apply List.filter_congr
      intro y hy
      have hne : y.1 ≠ x.1 := by
        intro h
        exact hn.1 (List.mem_map.mpr ⟨y, hy, h⟩)
      simp [hne]

end CriticalPercolation.MarkedTree

namespace CriticalPercolation.QueryTree
variable {E : Type*}

def pathNodes : (t : QueryTree E) → (E → Bool) → List t.Node
  | .stop, _ => []
  | .ask e l r, ω => .inl PUnit.unit ::
      if ω e then (r.pathNodes ω).map (Sum.inr ∘ Sum.inr)
      else (l.pathNodes ω).map (Sum.inr ∘ Sum.inl)

lemma map_bit_pathNodes (t : QueryTree E) (ω : E → Bool) :
    (t.pathNodes ω).map t.bit = t.reads ω := by
  induction t with
  | stop => rfl
  | ask e l r hl hr =>
    cases h : ω e <;> simp [pathNodes, reads, h, List.map_map, bit, hl, hr, Function.comp_def]

lemma mem_pathNodes (t : QueryTree E) (ω : E → Bool) (n : t.Node) :
    n ∈ t.pathNodes ω ↔ t.visits n ω := by
  induction t with
  | stop => exact PEmpty.elim n
  | ask e l r hl hr =>
    rcases n with a | (n | n)
    · cases a
      cases h : ω e <;> simp [pathNodes, visits, run, response, h]
    · cases h : ω e
      · simpa [pathNodes, visits, run, response, h] using hl n
      · simp [pathNodes, visits, run, response, h]
    · cases h : ω e
      · simp [pathNodes, visits, run, response, h]
      · simpa [pathNodes, visits, run, response, h] using hr n

lemma pathNodes_nodup (t : QueryTree E) (ω : E → Bool) : (t.pathNodes ω).Nodup := by
  induction t with
  | stop => simp [pathNodes]
  | ask e l r hl hr =>
    cases h : ω e
    · simp only [pathNodes, h, Bool.false_eq_true, ↓reduceIte, List.nodup_cons]
      refine ⟨by simp, hl.map ?_⟩
      exact Sum.inr_injective.comp Sum.inl_injective
    · simp only [pathNodes, h, ↓reduceIte, List.nodup_cons]
      refine ⟨by simp, hr.map ?_⟩
      exact Sum.inr_injective.comp Sum.inr_injective

def marked : (t : QueryTree E) → MarkedTree E t.Node
  | .stop => .stop
  | .ask e l r => .ask e (.inl PUnit.unit)
      (l.marked.map (Sum.inr ∘ Sum.inl)) (r.marked.map (Sum.inr ∘ Sum.inr))

lemma trace_marked (t : QueryTree E) (ω : E → Bool) :
    t.marked.trace ω = (t.pathNodes ω).map (fun n => (t.bit n, n)) := by
  induction t with
  | stop => rfl
  | ask e l r hl hr =>
    cases h : ω e <;>
      simp [marked, MarkedTree.trace, MarkedTree.trace_map, pathNodes, h,
        hl, hr, List.map_map, Function.comp_def, bit]

lemma mem_trace_marked (t : QueryTree E) (ω : E → Bool) (e : E) (n : t.Node) :
    (e,n) ∈ t.marked.trace ω ↔ t.bit n = e ∧ t.visits n ω := by
  rw [trace_marked]
  simp [List.mem_map, mem_pathNodes, Prod.mk.injEq, and_left_comm]

end CriticalPercolation.QueryTree

end
end

end OAI
