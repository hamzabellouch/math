import Mathlib.Algebra.BigOperators.Group.List.Basic
import OAI.NumberTheory.Ostmann.Tree.IncidenceCycle
import OAI.NumberTheory.Ostmann.Characters.CycleAction

namespace OAI

/-! # A balanced leaf action from an incidence-graph cycle -/

namespace Ostmann

open scoped BigOperators

theorem list_sum_finset_sum {X I R : Type*} [AddCommMonoid R]
    (xs : List X) (s : Finset I) (f : I → X → R) :
    (∑ i ∈ s, (xs.map (f i)).sum) = (xs.map fun x => ∑ i ∈ s, f i x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem walk_dart_difference {V R : Type*} [AddCommGroup R] {G : SimpleGraph V}
    {u v : V} (w : G.Walk u v) (f : V → R) :
    (w.darts.map fun d => f d.fst - f d.snd).sum = f u - f v := by
  induction w with
  | nil => simp
  | cons h w ih =>
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
    abel

theorem walk_dart_reverse_difference {V R : Type*} [AddCommGroup R] {G : SimpleGraph V}
    {u v : V} (w : G.Walk u v) (f : V → R) :
    (w.darts.map fun d => f d.snd - f d.fst).sum = f v - f u := by
  induction w with
  | nil => simp
  | cons h w ih =>
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
    abel

theorem incidenceDart_exists {L C Q : Type*} (component : L → C) (quartet : L → Q)
    (d : (incidenceGraph component quartet).Dart) :
    ∃ i : L,
      (d.fst = Sum.inl (component i) ∧ d.snd = Sum.inr (quartet i)) ∨
      (d.fst = Sum.inr (quartet i) ∧ d.snd = Sum.inl (component i)) := by
  rcases d with ⟨⟨x, y⟩, h⟩
  cases x with
  | inl c =>
    cases y with
    | inl c' => exact False.elim h
    | inr q =>
      obtain ⟨i, hc, hq⟩ := h
      exact ⟨i, Or.inl ⟨congrArg Sum.inl hc.symm, congrArg Sum.inr hq.symm⟩⟩
  | inr q =>
    cases y with
    | inr q' => exact False.elim h
    | inl c =>
      obtain ⟨i, hc, hq⟩ := h
      exact ⟨i, Or.inr ⟨congrArg Sum.inr hq.symm, congrArg Sum.inl hc.symm⟩⟩

noncomputable def incidenceDartLabel {L C Q : Type*} (component : L → C) (quartet : L → Q)
    (d : (incidenceGraph component quartet).Dart) : L :=
  Classical.choose (incidenceDart_exists component quartet d)

theorem incidenceDartLabel_spec {L C Q : Type*} (component : L → C) (quartet : L → Q)
    (d : (incidenceGraph component quartet).Dart) :
    (d.fst = Sum.inl (component (incidenceDartLabel component quartet d)) ∧
      d.snd = Sum.inr (quartet (incidenceDartLabel component quartet d))) ∨
    (d.fst = Sum.inr (quartet (incidenceDartLabel component quartet d)) ∧
      d.snd = Sum.inl (component (incidenceDartLabel component quartet d))) :=
  Classical.choose_spec (incidenceDart_exists component quartet d)

def incidenceDartSign {L C Q : Type*} {component : L → C} {quartet : L → Q}
    (d : (incidenceGraph component quartet).Dart) : ℤ :=
  match d.fst with
  | Sum.inl _ => 1
  | Sum.inr _ => -1

noncomputable def incidenceWalkSign {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (i : L) : ℤ :=
  (w.darts.map fun d => if incidenceDartLabel component quartet d = i then incidenceDartSign d else 0).sum

theorem incidenceWalkSign_block_sum {L C Q B : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq B] (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (block : L → B) (b : B) :
    (∑ i ∈ Finset.univ.filter (fun i => block i = b), incidenceWalkSign component quartet w i) =
      (w.darts.map fun d => if block (incidenceDartLabel component quartet d) = b
        then incidenceDartSign d else 0).sum := by
  unfold incidenceWalkSign
  rw [list_sum_finset_sum]
  congr 1
  apply List.map_congr_left
  intro d _
  simp

theorem incidenceDart_component_difference {L C Q : Type*} [DecidableEq C] [DecidableEq Q]
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart) (c : C) :
    (if component (incidenceDartLabel component quartet d) = c then incidenceDartSign d else 0) =
      (if d.fst = Sum.inl c then (1 : ℤ) else 0) - (if d.snd = Sum.inl c then 1 else 0) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · simp [incidenceDartSign, hfst, hsnd]
  · simp only [incidenceDartSign, hfst, hsnd, Sum.inl.injEq,
      Sum.inr_ne_inl, ite_false, zero_sub]
    split_ifs <;> rfl

theorem incidenceDart_quartet_difference {L C Q : Type*} [DecidableEq C] [DecidableEq Q]
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart) (q : Q) :
    (if quartet (incidenceDartLabel component quartet d) = q then incidenceDartSign d else 0) =
      (if d.snd = Sum.inr q then (1 : ℤ) else 0) - (if d.fst = Sum.inr q then 1 else 0) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · simp [incidenceDartSign, hfst, hsnd]
  · simp only [incidenceDartSign, hfst, hsnd, Sum.inr.injEq,
      Sum.inl_ne_inr, ite_false, zero_sub]
    split_ifs <;> rfl

theorem incidenceWalkSign_component_balanced {L C Q : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq C] [DecidableEq Q] (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (c : C) :
    (∑ i ∈ Finset.univ.filter (fun i => component i = c), incidenceWalkSign component quartet w i) = 0 := by
  rw [incidenceWalkSign_block_sum]
  simp_rw [incidenceDart_component_difference]
  simpa only [sub_self] using walk_dart_difference w
    (fun x : C ⊕ Q => if x = Sum.inl c then (1 : ℤ) else 0)

theorem incidenceWalkSign_quartet_balanced {L C Q : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq C] [DecidableEq Q] (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (q : Q) :
    (∑ i ∈ Finset.univ.filter (fun i => quartet i = q), incidenceWalkSign component quartet w i) = 0 := by
  rw [incidenceWalkSign_block_sum]
  simp_rw [incidenceDart_quartet_difference]
  simpa only [sub_self] using walk_dart_reverse_difference w
    (fun x : C ⊕ Q => if x = Sum.inr q then (1 : ℤ) else 0)

end Ostmann

end OAI
