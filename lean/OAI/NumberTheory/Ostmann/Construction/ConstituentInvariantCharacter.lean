import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchedCharacter
import OAI.NumberTheory.Ostmann.Construction.RetainedInvariantCharacter

namespace OAI

/-! # Actual original character signs survive every matching -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

noncomputable def scheduledRetainedCharacters {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (n : ℕ) :
    CopyScheduleH role n ⊕ CopyScheduleY role n → ∀ p : ℕ, DirichletCharacter ℂ p :=
  Sum.elim (fun h => χ (copyScheduleOrigin n h.val))
    (fun y => χ (copyScheduleOrigin n y.val))

theorem constituentCharacterCore_invariant_matching {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (hχ : ∀ h, χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val))
    (d d' : D) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let χR := scheduledRetainedCharacters ρ χ n
    let σ := Equiv.sumCongr e (Equiv.refl (CopyScheduleY ρ n))
    let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
    let ν := scheduledRetainedUnary ρ χ κ pivot n (hist d)
    let ω := scheduledRetainedUnary ρ χ κ pivot n (hist d')
    constituentCharacterCore role size χ κ pivot n P hP
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCore role size χ κ pivot n P hP
        childBound pivotBound ranges leaf hist u M (l ∘ e, d')) =
    (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l ∘ e, d'))) *
    finiteEdgeWeight (dirichletGraphEdge χR
      (graphDifference (retainedInternalGraph g) (transportGraph σ (retainedInternalGraph g))))
      (fun i x => externalPivotUnary χR g ν M i x *
        conj (externalPivotUnary χR g ω M (σ.symm i) x))
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) := by
  dsimp only
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let χR := scheduledRetainedCharacters ρ χ n
  let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
  let ν := scheduledRetainedUnary ρ χ κ pivot n (hist d)
  let ω := scheduledRetainedUnary ρ χ κ pivot n (hist d')
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  by_cases hp : Pairwise (fun i j =>
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j))
  · have he := retainedCharacterBranch_invariant_matching (fun h => (l h : ℕ))
      (fun y => (u y : ℕ)) e χR hχ g g ν ω M hp
      (fun i => scheduledRetainedGraph_diagonal ρ pivot n (some i))
      (fun i => scheduledRetainedGraph_diagonal ρ pivot n (some i))
    unfold constituentCharacterCore
    simp only [map_mul]
    calc
      _ = (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l, d) *
            conj (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l ∘ e, d'))) *
          (retainedCharacterBranch (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
            (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val)) g (fun h => ν (.inl h) (l h)) (fun y => ν (.inr y) (u y)) M *
          conj (retainedCharacterBranch (fun h => (l (e h) : ℕ)) (fun y => (u y : ℕ))
            (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val)) g (fun h => ω (.inl h) (l (e h))) (fun y => ω (.inr y) (u y)) M)) := by
              dsimp only [ν, ω, scheduledRetainedUnary, χR, scheduledRetainedCharacters, Sum.elim_inl, Sum.elim_inr, g, ρ, Function.comp_apply]
              ring
      _ = _ := by
        congr 1
  · have hw : constituentUnweightedTransferWeight role size n P childBound pivotBound ranges
        leaf hist u M (l, d) = 0 := by
      unfold constituentUnweightedTransferWeight
      exact ite_eq_right hp
    unfold constituentCharacterCore
    rw [hw]
    simp only [zero_mul]

end Ostmann

end OAI
