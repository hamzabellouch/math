import OAI.NumberTheory.Ostmann.Construction.FinalGraphIdentification
import OAI.NumberTheory.Ostmann.Tree.TwoVertexReindex

namespace OAI

/-! # A genuine nonprincipal factor for every distinct final reassignment pair -/

namespace Ostmann

open scoped Classical

theorem final_pair_one_sided_factor {n m : ℕ} {J : Type*} [Fintype J]
    (graph : FinalGraphVertex n m J → FinalGraphVertex n m J → ℤ)
    (hdiag : ∀ v, graph v v = 0)
    (α : Fin (n + 1) → ℤ) (hα : ∀ j, α j = 1 ∨ α j = -1)
    (hincoming : ∀ x j b, graph (.inr (.inl (j, b))) (.inl x) =
      anchorIncoming α (parityPathValue x.1) j b)
    (hregular : ∀ x j b, graph (.inl x) (.inr (.inl (j, b))) =
      finalCopyParity (parityPathValue x.1))
    (χ : FinalGraphVertex n m J → ∀ p : ℕ, DirichletCharacter ℂ p)
    (Q : FinalGraphVertex n m J → Finset ℕ)
    (hQ : ∀ j b, (Q (.inr (.inl (j, b)))).Nonempty)
    (hχ : ∀ j b q, q ∈ Q (.inr (.inl (j, b))) → χ (.inr (.inl (j, b))) q ^ 2 ≠ 1)
    (ν : FinalGraphVertex n m J → ℕ → ℂ) (hν : ∀ v p, ‖ν v p‖ ≤ 1)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    let G := graphDifference (finalReassignedGraph graph e) (finalReassignedGraph graph f)
    ∃ (a v : FinalGraphVertex n m J) (hav : a ≠ v),
      (∀ q ∈ Q a, χ a q ^ G a v ≠ 1) ∧ G v a = 0 ∧
      ∀ outside : OtherVertices a v → ℕ, ∃ U W : ℕ → ℂ,
        (∀ p, ‖U p‖ ≤ 1) ∧ (∀ q, ‖W q‖ ≤ 1) ∧
        ∀ q p, finiteEdgeWeight (dirichletGraphEdge χ G) ν
          (fun i => twoVertexLabels outside q p ((twoVertexEquiv a v hav).symm i)) =
            U p * W q * (χ a q ^ G a v) (p : ZMod q) := by
  dsimp only
  let G := graphDifference (finalReassignedGraph graph e) (finalReassignedGraph graph f)
  obtain ⟨x, j, b, hnp, hr⟩ := final_reassignment_graph_character graph α hα hincoming hregular
    (fun j b => χ (.inr (.inl (j, b)))) (fun j b => Q (.inr (.inl (j, b)))) hχ e f hef
  let a : FinalGraphVertex n m J := .inr (.inl (j, b))
  let v : FinalGraphVertex n m J := .inl x
  have hav : a ≠ v := by simp only [a, v, ne_eq, reduceCtorEq, not_false_eq_true]
  refine ⟨a, v, hav, hnp, hr, ?_⟩
  intro outside
  have hfwd : G a v ≠ 0 := by
    obtain ⟨q, hq⟩ := hQ j b
    intro hz
    have hn := hnp q hq
    simp only [show graphDifference (finalReassignedGraph graph e) (finalReassignedGraph graph f)
      (.inr (.inl (j, b))) (.inl x) = 0 from hz, zpow_zero, ne_eq, not_true_eq_false] at hn
  exact selected_graph_factorization a v hav χ G ν outside hν
    ⟨finalReassignedGraph_diagonal graph hdiag e f a, finalReassignedGraph_diagonal graph hdiag e f v⟩ hr hfwd

end Ostmann

end OAI
