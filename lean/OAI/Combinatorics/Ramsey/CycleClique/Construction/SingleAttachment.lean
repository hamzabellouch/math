import OAI.Combinatorics.Ramsey.CycleClique.Construction.EndpointFullAttachment

namespace OAI

/-! Deleting a set with one attachment preserves connectivity. -/

namespace CycleClique.Construction
theorem connected_outside_single_attachment {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) {E : Finset V} {u : V} (hu : u ∉ E)
    (hattach : ∀ e ∈ E, ∀ v, G.Adj e v → v ∉ E → v = u) :
    (G.induce {v | v ∉ E}).Connected := by
  classical
  let f : V → {v : V | v ∉ E} := fun v => if hv : v ∈ E then ⟨u, hu⟩ else ⟨v, hv⟩
  let : Nonempty {v : V | v ∉ E} := ⟨⟨u, hu⟩⟩
  have hedge : ∀ a b, G.Adj a b →
      (G.induce {v | v ∉ E}).Reachable (f a) (f b) := by
    intro a b hab
    by_cases ha : a ∈ E
    · by_cases hb : b ∈ E
      · simp only [f, dite_eq_left ha, dite_eq_left hb]
        exact SimpleGraph.Reachable.refl _
      · have heq := hattach a ha b hab hb
        subst b
        simp only [f, dite_eq_left ha, dite_eq_right hu]
        exact SimpleGraph.Reachable.refl _
    · by_cases hb : b ∈ E
      · have heq := hattach b hb a hab.symm ha
        subst a
        simp only [f, dite_eq_right hu, dite_eq_left hb]
        exact SimpleGraph.Reachable.refl _
      · simp only [f, dite_eq_right ha, dite_eq_right hb]
        exact (show (G.induce {v | v ∉ E}).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab).reachable
  have hmap : ∀ a b, G.Reachable a b →
      (G.induce {v | v ∉ E}).Reachable (f a) (f b) := by
    intro a b hr
    obtain ⟨p⟩ := hr
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab p ih => exact (hedge a b hab).trans ih
  refine ⟨?_⟩
  intro a b
  have h := hmap a.val b.val (hconn a.val b.val)
  simpa only [f, dite_eq_right a.property, dite_eq_right b.property] using h

theorem neighbors_outside_single_attachment {V : Type*} {G : SimpleGraph V}
    {E : Finset V} {u v : V} (hv : v ∉ E) (hvu : v ≠ u)
    (hattach : ∀ e ∈ E, ∀ w, G.Adj e w → w ∉ E → w = u) :
    G.neighborSet v ⊆ {w | w ∉ E} := by
  intro w hvw hw
  exact hvu (hattach w hw v hvw.symm hv)

theorem degree_outside_single_attachment {V : Type*} [Fintype V] {G : SimpleGraph V}
    {E : Finset V} {u : V} (v : {v : V | v ∉ E}) (hvu : v.val ≠ u)
    (hattach : ∀ e ∈ E, ∀ w, G.Adj e w → w ∉ E → w = u) :
    ((G.induce {v | v ∉ E}).neighborSet v).ncard = (G.neighborSet v.val).ncard := by
  classical
  simp only [SimpleGraph.ncard_neighborSet]
  exact G.degree_induce_of_neighborSet_subset
    (neighbors_outside_single_attachment v.property hvu hattach)

end CycleClique.Construction

end OAI
