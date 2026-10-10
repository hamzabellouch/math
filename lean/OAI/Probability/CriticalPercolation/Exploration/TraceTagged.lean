import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Tagged

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

lemma trace_tagged (coord : A → E) (t : MarkedTree E A) (ht : t.Tagged coord)
    (ω : E → Bool) (x : E × A) (hx : x ∈ t.trace ω) : x.1 = coord x.2 := by
  induction t with
  | stop => simp [trace] at hx
  | ask e a l r hl hr =>
    cases he : ω e <;> simp only [trace, he, Bool.false_eq_true, ↓reduceIte,
        List.mem_cons] at hx
    · rcases hx with rfl | hx
      · exact ht.1
      · exact hl ht.2.1 hx
    · rcases hx with rfl | hx
      · exact ht.1
      · exact hr ht.2.2 hx

lemma trace_labels_nodup [DecidableEq E] (coord : A → E) (t : MarkedTree E A)
    (ht : t.Tagged coord) (hv : t.bare.Valid ∅) (ω : E → Bool) :
    ((t.trace ω).map Prod.snd).Nodup := by
  have he : ((t.trace ω).map Prod.snd).map coord = (t.trace ω).map Prod.fst := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact (trace_tagged coord t ht ω x hx).symm
  apply List.Nodup.of_map coord
  rw [he, trace_bits]
  exact reads_nodup _ _ hv ω

lemma list_label_sum [DecidableEq A] (xs : List A) (hn : xs.Nodup) (a : A) (v : ℝ) :
    (xs.map (fun b => if b = a then v else 0)).sum = if a ∈ xs then v else 0 := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.sum_cons, ih hn.2]
    by_cases h : b = a
    · subst b
      simp [hn.1]
    · by_cases ha : a ∈ xs <;> simp [h, ha, Ne.symm h]

lemma sum_tagged_visits [DecidableEq E] [DecidableEq A] (coord : A → E)
    (t : MarkedTree E A) (ht : t.Tagged coord) (hv : t.bare.Valid ∅)
    (ω : E → Bool) (a : A) (v : E → ℝ) :
    (∑ n : t.bare.Node, if t.nodeLabel n = a then
      (if t.bare.visits n ω then v (t.bare.bit n) else 0) else 0) =
      if (coord a,a) ∈ t.trace ω then v (coord a) else 0 := by
  have hn := trace_labels_nodup coord t ht hv ω
  have hm : a ∈ (t.trace ω).map Prod.snd ↔ (coord a,a) ∈ t.trace ω := by
    constructor
    · intro ha
      rcases List.mem_map.mp ha with ⟨x,hx,hxa⟩
      have he : x = (coord a,a) := Prod.ext (by rw [trace_tagged coord t ht ω x hx, hxa]) hxa
      rwa [← he]
    · intro ha
      exact List.mem_map.mpr ⟨_,ha,rfl⟩
  calc
    _ = ∑ n : t.bare.Node, if t.bare.visits n ω then
        (if t.nodeLabel n = a then v (coord a) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [t.tagged_bit coord ht n]
      split_ifs <;> simp_all
    _ = ((t.trace ω).map (fun x => if x.2 = a then v (coord a) else 0)).sum :=
      sum_visited_nodes t ω (fun _ b => if b = a then v (coord a) else 0)
    _ = if a ∈ (t.trace ω).map Prod.snd then v (coord a) else 0 := by
      simpa only [List.map_map, Function.comp_def] using
        list_label_sum ((t.trace ω).map Prod.snd) hn a (v (coord a))
    _ = _ := by simp only [hm]

lemma pooled_input_sum [Fintype E] [DecidableEq E] [DecidableEq A]
    (coord : A → E) (t : MarkedTree E A) (ht : t.Tagged coord) (hv : t.bare.Valid ∅)
    (P : (E → Bool) → ℝ) (f : (E → Bool) → E → ℝ) (a : A) :
    (∑ n : t.bare.Node, if t.nodeLabel n = a then
      (∑ ω, if t.bare.visits n ω then P ω*f ω (t.bare.bit n) else 0) else 0) =
      ∑ ω, if (coord a,a) ∈ t.trace ω then P ω*f ω (coord a) else 0 := by
  trans ∑ n : t.bare.Node, ∑ ω, if t.nodeLabel n = a then
    (if t.bare.visits n ω then P ω*f ω (t.bare.bit n) else 0) else 0
  · apply Finset.sum_congr rfl
    intro n _
    by_cases h : t.nodeLabel n = a <;> simp [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  exact sum_tagged_visits coord t ht hv ω a (fun e => P ω*f ω e)

end CriticalPercolation.MarkedTree

open Set MeasureTheory
open scoped Classical

end
end

end OAI
