import OAI.NumberTheory.Ostmann.Characters.AnchorGraphEvolution
import OAI.NumberTheory.Ostmann.Construction.MatchedGraphQuotient

namespace OAI

/-! # The actual anchor/bulk edge in a final reassignment quotient -/

namespace Ostmann

abbrev FinalGraphVertex (n m : ℕ) (J : Type*) :=
  (ParityPathSum n × Fin m) ⊕ ((Fin (n + 1) × Bool) ⊕ J)

def finalVertexPerm {n m : ℕ} {J : Type*} (e : FinalParityReassignments n m) :
    Equiv.Perm (FinalGraphVertex n m J) :=
  Equiv.sumCongr (paritySlotPerm e) (Equiv.refl _)

def finalReassignedGraph {n m : ℕ} {J : Type*}
    (graph : FinalGraphVertex n m J → FinalGraphVertex n m J → ℤ)
    (e : FinalParityReassignments n m) (x y : FinalGraphVertex n m J) : ℤ :=
  graph (finalVertexPerm e x) (finalVertexPerm e y)

theorem finalReassignedGraph_diagonal {n m : ℕ} {J : Type*}
    (graph : FinalGraphVertex n m J → FinalGraphVertex n m J → ℤ)
    (hdiag : ∀ x, graph x x = 0) (e f : FinalParityReassignments n m)
    (x : FinalGraphVertex n m J) :
    graphDifference (finalReassignedGraph graph e) (finalReassignedGraph graph f) x x = 0 := by
  simp only [graphDifference, finalReassignedGraph, hdiag, sub_self]

/-- The coefficient formulas are the output of anchor creation, subsequent
outside-anchor copies, and regularity of bulk rows. All other edges are arbitrary. -/
theorem final_reassignment_graph_interaction {n m : ℕ} {J : Type*}
    (graph : FinalGraphVertex n m J → FinalGraphVertex n m J → ℤ)
    (α : Fin (n + 1) → ℤ) (hα : ∀ j, α j = 1 ∨ α j = -1)
    (hincoming : ∀ x j b, graph (.inr (.inl (j, b))) (.inl x) =
      anchorIncoming α (parityPathValue x.1) j b)
    (hregular : ∀ x j b, graph (.inl x) (.inr (.inl (j, b))) =
      finalCopyParity (parityPathValue x.1))
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (x : ParityPathSum n × Fin m) (j : Fin (n + 1)) (b : Bool),
      let G := graphDifference (finalReassignedGraph graph e) (finalReassignedGraph graph f)
      (G (.inr (.inl (j, b))) (.inl x) = 2 ∨ G (.inr (.inl (j, b))) (.inl x) = -2) ∧
        G (.inl x) (.inr (.inl (j, b))) = 0 := by
  obtain ⟨x, j, b, h⟩ := final_reassignment_interaction α hα e f hef
  refine ⟨x, j, b, ?_⟩
  simpa only [graphDifference, finalReassignedGraph, finalVertexPerm,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply, hincoming, hregular, anchorIncoming] using h

/-- The character at the small anchor is a genuine nonprincipal signed square. -/
theorem final_reassignment_graph_character {n m : ℕ} {J : Type*}
    (graph : FinalGraphVertex n m J → FinalGraphVertex n m J → ℤ)
    (α : Fin (n + 1) → ℤ) (hα : ∀ j, α j = 1 ∨ α j = -1)
    (hincoming : ∀ x j b, graph (.inr (.inl (j, b))) (.inl x) =
      anchorIncoming α (parityPathValue x.1) j b)
    (hregular : ∀ x j b, graph (.inl x) (.inr (.inl (j, b))) =
      finalCopyParity (parityPathValue x.1))
    (χ : Fin (n + 1) → Bool → ∀ q : ℕ, DirichletCharacter ℂ q)
    (Q : Fin (n + 1) → Bool → Finset ℕ)
    (hχ : ∀ j b q, q ∈ Q j b → χ j b q ^ 2 ≠ 1)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (x : ParityPathSum n × Fin m) (j : Fin (n + 1)) (b : Bool),
      let G := graphDifference (finalReassignedGraph graph e) (finalReassignedGraph graph f)
      (∀ q ∈ Q j b, χ j b q ^ G (.inr (.inl (j, b))) (.inl x) ≠ 1) ∧
        G (.inl x) (.inr (.inl (j, b))) = 0 := by
  obtain ⟨x, j, b, hforward, hreverse⟩ :=
    final_reassignment_graph_interaction graph α hα hincoming hregular e f hef
  exact ⟨x, j, b, (fun q hq => signed_square_nonprincipal (χ j b q) (hχ j b q hq) _ hforward), hreverse⟩

end Ostmann

end OAI
