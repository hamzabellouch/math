import OAI.NumberTheory.Ostmann.Construction.TransferCompletePhase
import OAI.NumberTheory.Ostmann.Construction.MatchedRetainedPhase

namespace OAI

/-! # The matched character branch as its actual directed graph quotient -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem retainedCharacterBranch_eq_edge {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (χ : H ⊕ Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : H ⊕ Y → ℕ → ℂ) (M : ℕ) :
    retainedCharacterBranch L U (fun h => χ (.inl h)) (fun y => χ (.inr y)) b
      (fun h => ν (.inl h) (L h)) (fun y => ν (.inr y) (U y)) M =
    finiteEdgeWeight (dirichletGraphEdge χ (retainedInternalGraph b))
      (externalPivotUnary χ b ν M) (Sum.elim L U) := by
  simp only [retainedCharacterBranch, finiteEdgeWeight, Fintype.prod_sum_type,
    externalPivotUnary, retainedInternalGraph, retainedGraphRow, dirichletGraphEdge,
    Sum.elim_inl, Sum.elim_inr, mul_assoc]
  congr 1

theorem finiteEdgeWeight_common_transport {V : Type*} [Fintype V]
    (e : Equiv.Perm V) (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : V → V → ℤ) (ν : V → ℕ → ℂ) (p : V → ℕ) :
    finiteEdgeWeight (dirichletGraphEdge (fun _ => χ) b) ν (p ∘ e) =
      finiteEdgeWeight (dirichletGraphEdge (fun _ => χ) (transportGraph e b))
        (fun i => ν (e.symm i)) p := by
  simpa only [finiteEdgeWeight, Function.comp_def, transportGraph, dirichletGraphEdge, Equiv.symm_apply_apply] using
    finiteEdgeWeight_equiv e (dirichletGraphEdge (fun _ => χ) (transportGraph e b))
      (fun i => ν (e.symm i)) p

theorem retainedCharacterBranch_common_matching {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (e : Equiv.Perm H) (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (b c : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν ω : H ⊕ Y → ℕ → ℂ) (M : ℕ)
    (hp : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hb : ∀ i, b (some i) (some i) = 0) (hc : ∀ i, c (some i) (some i) = 0) :
    let : ∀ h, Fact ((L ∘ e) h).Prime := fun h => inferInstanceAs (Fact (L (e h)).Prime)
    let σ := Equiv.sumCongr e (Equiv.refl Y)
    retainedCharacterBranch L U (fun _ => χ) (fun _ => χ) b
      (fun h => ν (.inl h) (L h)) (fun y => ν (.inr y) (U y)) M *
      conj (retainedCharacterBranch (L ∘ e) U (fun _ => χ) (fun _ => χ) c
        (fun h => ω (.inl h) (L (e h))) (fun y => ω (.inr y) (U y)) M) =
    finiteEdgeWeight (dirichletGraphEdge (fun _ => χ)
      (graphDifference (retainedInternalGraph b) (transportGraph σ (retainedInternalGraph c))))
      (fun i x => externalPivotUnary (fun _ => χ) b ν M i x *
        conj (externalPivotUnary (fun _ => χ) c ω M (σ.symm i) x)) (Sum.elim L U) := by
  let : ∀ h, Fact ((L ∘ e) h).Prime := fun h => inferInstanceAs (Fact (L (e h)).Prime)
  dsimp only
  let σ := Equiv.sumCongr e (Equiv.refl Y)
  rw [retainedCharacterBranch_eq_edge L U (fun _ => χ) b ν M]
  have hr := retainedCharacterBranch_eq_edge (L ∘ e) U (fun _ => χ) c ω M
  simp only [Function.comp_apply] at hr
  rw [hr]
  have he : Sum.elim (L ∘ e) U = Sum.elim L U ∘ σ := by
    funext i
    cases i <;> rfl
  rw [he, finiteEdgeWeight_common_transport σ χ]
  exact dirichlet_graph_quotient (fun _ => χ) (retainedInternalGraph b)
    (transportGraph σ (retainedInternalGraph c)) _ _ _ hp hb (fun i => hc (σ.symm i))

end Ostmann

end OAI
