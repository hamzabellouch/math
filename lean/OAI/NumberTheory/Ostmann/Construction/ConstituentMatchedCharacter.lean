import OAI.NumberTheory.Ostmann.Construction.ConstituentCharacterCore
import OAI.NumberTheory.Ostmann.Construction.RetainedCharacterGraph

namespace OAI

/-! # The actual supported character core in a matched diagonal pair -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def scheduledRetainedUnary {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ) (pivot : ℕ → I)
    (n : ℕ) (t : FrequencyTree ℤ n) : CopyScheduleH role n ⊕ CopyScheduleY role n → ℕ → ℂ :=
  Sum.elim
    (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t h.val)
    (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t y.val)

theorem scheduledRetainedUnary_norm {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ) (pivot : ℕ → I)
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (n : ℕ) (t : FrequencyTree ℤ n)
    (i : CopyScheduleH role n ⊕ CopyScheduleY role n) (p : ℕ) :
    ‖scheduledRetainedUnary role χ κ pivot n t i p‖ ≤ 1 := by
  have hinit (i : I) (v : ℤ) (p : ℕ) : ‖initialRegularUnary χ κ i v p‖ ≤ 1 := by
    dsimp only [initialRegularUnary, regularUnary]
    rw [norm_mul]
    exact (mul_le_mul (hκ i p) (character_zpow_norm_le_one _ _ _)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  cases i with
  | inl h => exact copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _ hinit n t h.val p
  | inr y => exact copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _ hinit n t y.val p

theorem constituentCharacterCore_common_matching {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (d d' : D) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let σ := Equiv.sumCongr e (Equiv.refl (CopyScheduleY ρ n))
    let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
    let ν := scheduledRetainedUnary ρ (fun _ => χ) κ pivot n (hist d)
    let ω := scheduledRetainedUnary ρ (fun _ => χ) κ pivot n (hist d')
    constituentCharacterCore role size (fun _ => χ) κ pivot n P hP
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCore role size (fun _ => χ) κ pivot n P hP
        childBound pivotBound ranges leaf hist u M (l ∘ e, d')) =
    (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l ∘ e, d'))) *
    finiteEdgeWeight (dirichletGraphEdge (fun _ => χ)
      (graphDifference (retainedInternalGraph g) (transportGraph σ (retainedInternalGraph g))))
      (fun i x => externalPivotUnary (fun _ => χ) g ν M i x *
        conj (externalPivotUnary (fun _ => χ) g ω M (σ.symm i) x))
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) := by
  dsimp only
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
  let ν := scheduledRetainedUnary ρ (fun _ => χ) κ pivot n (hist d)
  let ω := scheduledRetainedUnary ρ (fun _ => χ) κ pivot n (hist d')
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  by_cases hp : Pairwise (fun i j =>
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j))
  · have he := retainedCharacterBranch_common_matching (fun h => (l h : ℕ))
      (fun y => (u y : ℕ)) e χ g g ν ω M hp
      (fun i => scheduledRetainedGraph_diagonal ρ pivot n (some i))
      (fun i => scheduledRetainedGraph_diagonal ρ pivot n (some i))
    unfold constituentCharacterCore
    simp only [map_mul]
    calc
      _ = (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l, d) *
            conj (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l ∘ e, d'))) *
          (retainedCharacterBranch (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
            (fun _ => χ) (fun _ => χ) g (fun h => ν (.inl h) (l h)) (fun y => ν (.inr y) (u y)) M *
          conj (retainedCharacterBranch (fun h => (l (e h) : ℕ)) (fun y => (u y : ℕ))
            (fun _ => χ) (fun _ => χ) g (fun h => ω (.inl h) (l (e h))) (fun y => ω (.inr y) (u y)) M)) := by
              dsimp only [ν, ω, scheduledRetainedUnary, Sum.elim_inl, Sum.elim_inr, g, ρ, Function.comp_apply]
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
