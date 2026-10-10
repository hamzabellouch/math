import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace OAI

/-!
# A cycle in the component--quartet incidence diagram

There is one edge per leaf. Parallel edges already give the two-edge
cycle used in the manuscript; otherwise the incidence graph is simple,
and at least as many edges as vertices force a cycle.
-/

namespace Ostmann

/-- A finite forest on a nonempty vertex set has fewer edges than vertices. -/
theorem forest_card_edges_lt {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (hG : G.IsAcyclic) :
    G.edgeFinset.card < Fintype.card V := by
  classical
  obtain ⟨T, hGT, _, hT⟩ :=
    (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
      (show G ≤ ⊤ from le_top) hG
  have hcard := hT.card_edgeFinset
  have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
  omega

theorem exists_cycle_of_card_edges_ge {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (hcard : Fintype.card V ≤ G.edgeFinset.card) :
    ∃ v : V, ∃ c : G.Walk v v, c.IsCycle := by
  classical
  have h : ¬G.IsAcyclic := fun hG => (not_lt_of_ge hcard) (forest_card_edges_lt G hG)
  unfold SimpleGraph.IsAcyclic at h
  push Not at h
  exact h

def incidenceGraph {L C Q : Type*} (component : L → C) (quartet : L → Q) :
    SimpleGraph (C ⊕ Q) where
  Adj x y := match x, y with
    | .inl c, .inr q => ∃ i, component i = c ∧ quartet i = q
    | .inr q, .inl c => ∃ i, component i = c ∧ quartet i = q
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact not_false⟩

/-- The incidence diagram has either parallel leaves or a genuine simple cycle. -/
theorem incidence_parallel_or_cycle {L C Q : Type*} [Fintype L] [Fintype C] [Fintype Q]
    [Nonempty L] (component : L → C) (quartet : L → Q)
    (hcard : Fintype.card C + Fintype.card Q ≤ Fintype.card L) :
    (∃ i j : L, i ≠ j ∧ component i = component j ∧ quartet i = quartet j) ∨
      ∃ v : C ⊕ Q, ∃ c : (incidenceGraph component quartet).Walk v v, c.IsCycle := by
  classical
  by_cases hinj : Function.Injective (fun i => (component i, quartet i))
  · right
    let : Nonempty (C ⊕ Q) := ⟨.inl (component (Classical.choice ‹Nonempty L›))⟩
    let G := incidenceGraph component quartet
    let edge : L → G.edgeFinset := fun i =>
      ⟨s(Sum.inl (component i), Sum.inr (quartet i)), by
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact ⟨i, rfl, rfl⟩⟩
    have hedge : Function.Injective edge := by
      intro i j hij
      have he := congrArg (fun e : G.edgeFinset => e.1) hij
      rcases Sym2.eq_iff.mp he with h | h
      · apply hinj
        exact Prod.ext (Sum.inl.inj h.1) (Sum.inr.inj h.2)
      · cases h.1
    have hle := Fintype.card_le_of_injective edge hedge
    have hV : Fintype.card (C ⊕ Q) ≤ G.edgeFinset.card := by
      simpa only [Fintype.card_sum, Fintype.card_coe] using hcard.trans hle
    exact exists_cycle_of_card_edges_ge G hV
  · left
    simp only [Function.Injective, Prod.mk.injEq, not_forall] at hinj
    obtain ⟨i, j, ⟨hc, hq⟩, hne⟩ := hinj
    exact ⟨i, j, hne, hc, hq⟩

end Ostmann

end OAI
