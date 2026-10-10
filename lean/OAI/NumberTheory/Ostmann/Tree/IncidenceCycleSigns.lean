import OAI.NumberTheory.Ostmann.Tree.IncidenceCirculation
import OAI.NumberTheory.Ostmann.Tree.ParallelCycle

namespace OAI

/-! # The nonzero balanced sign vector supplied by an incidence cycle -/

namespace Ostmann

open scoped BigOperators

theorem list_label_sum_eq_zero {X L R : Type*} [DecidableEq L] [AddCommMonoid R]
    (xs : List X) (label : X → L) (f : X → R) (i : L) (hi : i ∉ xs.map label) :
    (xs.map fun x => if label x = i then f x else 0).sum = 0 := by
  apply List.sum_eq_zero
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  have hne : label x ≠ i := fun h => hi (List.mem_map.mpr ⟨x, hx, h⟩)
  simp only [hne, ite_false]

theorem list_label_sum_of_mem {X L R : Type*} [DecidableEq L] [AddCommMonoid R]
    (xs : List X) (label : X → L) (f : X → R) (h : (xs.map label).Nodup)
    (x : X) (hx : x ∈ xs) :
    (xs.map fun y => if label y = label x then f y else 0).sum = f x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with hxy | hx
    · subst x
      simp only [List.map_cons, List.sum_cons, ite_true]
      rw [list_label_sum_eq_zero ys label f (label y) h.1, add_zero]
    · have hne : label y ≠ label x := fun heq => h.1 (List.mem_map.mpr ⟨x, hx, heq.symm⟩)
      simp only [List.map_cons, List.sum_cons, hne, ite_false, zero_add]
      exact ih h.2 hx

theorem incidenceDart_edge_of_label {L C Q : Type*}
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart) :
    d.edge = s(Sum.inl (component (incidenceDartLabel component quartet d)),
      Sum.inr (quartet (incidenceDartLabel component quartet d))) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · simp only [SimpleGraph.Dart.edge, hfst, hsnd]
  · simp only [SimpleGraph.Dart.edge, hfst, hsnd, Sym2.eq_swap]

theorem incidenceWalk_labels_nodup {L C Q : Type*}
    (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (hw : w.IsTrail) :
    (w.darts.map (incidenceDartLabel component quartet)).Nodup := by
  let edge : L → Sym2 (C ⊕ Q) := fun i => s(Sum.inl (component i), Sum.inr (quartet i))
  have hmap : (w.darts.map (incidenceDartLabel component quartet)).map edge = w.edges := by
    rw [List.map_map, SimpleGraph.Walk.edges]
    apply List.map_congr_left
    intro d _
    exact (incidenceDart_edge_of_label component quartet d).symm
  exact List.Nodup.of_map edge (hmap.symm ▸ hw.edges_nodup)

theorem incidenceDartSign_eq_one_or_neg_one {L C Q : Type*}
    {component : L → C} {quartet : L → Q} (d : (incidenceGraph component quartet).Dart) :
    incidenceDartSign d = 1 ∨ incidenceDartSign d = -1 := by
  unfold incidenceDartSign
  cases d.fst <;> simp

theorem incidenceWalkSign_values {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (hw : w.IsTrail) (i : L) :
    incidenceWalkSign component quartet w i = 0 ∨
      incidenceWalkSign component quartet w i = 1 ∨ incidenceWalkSign component quartet w i = -1 := by
  by_cases hi : i ∈ w.darts.map (incidenceDartLabel component quartet)
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hi
    right
    rw [incidenceWalkSign, list_label_sum_of_mem _ _ _ (incidenceWalk_labels_nodup component quartet w hw) d hd]
    exact incidenceDartSign_eq_one_or_neg_one d
  · left
    exact list_label_sum_eq_zero _ _ _ i hi

theorem incidenceCycleSign_nonzero {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (hw : w.IsCycle) :
    ∃ i : L, incidenceWalkSign component quartet w i = 1 ∨ incidenceWalkSign component quartet w i = -1 := by
  have hne : w.darts ≠ [] := fun h => hw.not_nil (SimpleGraph.Walk.darts_eq_nil.mp h)
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil w.darts hne
  refine ⟨incidenceDartLabel component quartet d, ?_⟩
  rw [incidenceWalkSign, list_label_sum_of_mem _ _ _
    (incidenceWalk_labels_nodup component quartet w hw.isTrail) d hd]
  exact incidenceDartSign_eq_one_or_neg_one d

/-- The edge/vertex count produces an actual nontrivial, balanced reciprocal leaf action. -/
theorem exists_balanced_incidence_sign {L C Q : Type*}
    [Fintype L] [Fintype C] [Fintype Q] [Nonempty L]
    [DecidableEq L] [DecidableEq C] [DecidableEq Q]
    (component : L → C) (quartet : L → Q)
    (hcard : Fintype.card C + Fintype.card Q ≤ Fintype.card L) :
    ∃ sign : L → ℤ,
      (∃ i, sign i = 1 ∨ sign i = -1) ∧
      (∀ i, sign i = 0 ∨ sign i = 1 ∨ sign i = -1) ∧
      (∀ c, (∑ i ∈ Finset.univ.filter (fun i => component i = c), sign i) = 0) ∧
      (∀ q, (∑ i ∈ Finset.univ.filter (fun i => quartet i = q), sign i) = 0) := by
  rcases incidence_parallel_or_cycle component quartet hcard with ⟨i, j, hij, hc, hq⟩ | ⟨v, w, hw⟩
  · refine ⟨parallelCycleSign i j, ⟨i, Or.inl (parallelCycleSign_left i j hij)⟩, ?_,
      parallelCycleSign_balanced component i j hc, parallelCycleSign_balanced quartet i j hq⟩
    intro k
    by_cases hki : k = i
    · subst k; exact Or.inr (Or.inl (parallelCycleSign_left i j hij))
    by_cases hkj : k = j
    · subst k; exact Or.inr (Or.inr (parallelCycleSign_right i j hij))
    exact Or.inl (parallelCycleSign_other i j k hki hkj)
  · exact ⟨incidenceWalkSign component quartet w, incidenceCycleSign_nonzero component quartet w hw,
      incidenceWalkSign_values component quartet w hw.isTrail,
      incidenceWalkSign_component_balanced component quartet w,
      incidenceWalkSign_quartet_balanced component quartet w⟩

end Ostmann

end OAI
