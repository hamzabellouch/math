import OAI.NumberTheory.Ostmann.Construction.RetainedCharacterGraph

namespace OAI

/-! # Matching preserves the character carried by each moved slot -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem finiteEdgeWeight_invariant_transport {V : Type*} [Fintype V]
    (e : Equiv.Perm V) (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ i, χ (e i) = χ i) (b : V → V → ℤ) (ν : V → ℕ → ℂ) (p : V → ℕ) :
    finiteEdgeWeight (dirichletGraphEdge χ b) ν (p ∘ e) =
      finiteEdgeWeight (dirichletGraphEdge χ (transportGraph e b))
        (fun i => ν (e.symm i)) p := by
  simpa only [finiteEdgeWeight, Function.comp_def, transportGraph, dirichletGraphEdge,
    Equiv.symm_apply_apply, hχ] using
      finiteEdgeWeight_equiv e (dirichletGraphEdge χ (transportGraph e b))
        (fun i => ν (e.symm i)) p

theorem retainedCharacterBranch_invariant_matching {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (e : Equiv.Perm H) (χ : H ⊕ Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ h, χ (.inl (e h)) = χ (.inl h))
    (b c : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν ω : H ⊕ Y → ℕ → ℂ) (M : ℕ)
    (hp : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hb : ∀ i, b (some i) (some i) = 0) (hc : ∀ i, c (some i) (some i) = 0) :
    let : ∀ h, Fact ((L ∘ e) h).Prime := fun h => inferInstanceAs (Fact (L (e h)).Prime)
    let σ := Equiv.sumCongr e (Equiv.refl Y)
    retainedCharacterBranch L U (fun h => χ (.inl h)) (fun y => χ (.inr y)) b
      (fun h => ν (.inl h) (L h)) (fun y => ν (.inr y) (U y)) M *
      conj (retainedCharacterBranch (L ∘ e) U (fun h => χ (.inl h)) (fun y => χ (.inr y)) c
        (fun h => ω (.inl h) (L (e h))) (fun y => ω (.inr y) (U y)) M) =
    finiteEdgeWeight (dirichletGraphEdge χ
      (graphDifference (retainedInternalGraph b) (transportGraph σ (retainedInternalGraph c))))
      (fun i x => externalPivotUnary χ b ν M i x *
        conj (externalPivotUnary χ c ω M (σ.symm i) x)) (Sum.elim L U) := by
  let : ∀ h, Fact ((L ∘ e) h).Prime := fun h => inferInstanceAs (Fact (L (e h)).Prime)
  dsimp only
  let σ := Equiv.sumCongr e (Equiv.refl Y)
  have hσ (i) : χ (σ i) = χ i := by cases i with
    | inl h => exact hχ h
    | inr y => rfl
  rw [retainedCharacterBranch_eq_edge L U χ b ν M]
  have hr := retainedCharacterBranch_eq_edge (L ∘ e) U χ c ω M
  simp only [Function.comp_apply] at hr
  rw [hr]
  have he : Sum.elim (L ∘ e) U = Sum.elim L U ∘ σ := by
    funext i
    cases i <;> rfl
  rw [he, finiteEdgeWeight_invariant_transport σ χ hσ]
  exact dirichlet_graph_quotient χ (retainedInternalGraph b)
    (transportGraph σ (retainedInternalGraph c)) _ _ _ hp hb (fun i => hc (σ.symm i))

end Ostmann

end OAI
