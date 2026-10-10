import OAI.NumberTheory.Ostmann.Construction.ConstituentInvariantCharacter
import OAI.NumberTheory.Ostmann.Construction.InsertedConstituentFourier

namespace OAI

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem constituentCharacterCore_invariant_pair_fourier {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hist : D → FrequencyTree ℤ n)
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
        childBound pivotBound ranges (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M (l, d) *
      conj (constituentCharacterCore role size χ κ pivot n P hP
        childBound pivotBound ranges (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M (l ∘ e, d')) =
    if Pairwise (fun i j =>
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j)) then
      (groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
          childBound pivotBound ranges ψ X lo hi (hist d)
          (insertedConstituentValues role size n M (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) *
        conj (groupedFullCoprimeFourierWeight role n
          (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
          childBound pivotBound ranges ψ X lo hi (hist d')
          (insertedConstituentValues role size n M (fun h => (l h : ℕ)) (fun y => (u y : ℕ))))) *
    finiteEdgeWeight (dirichletGraphEdge χR
      (graphDifference (retainedInternalGraph g) (transportGraph σ (retainedInternalGraph g))))
      (fun i x => externalPivotUnary χR g ν M i x *
        conj (externalPivotUnary χR g ω M (σ.symm i) x))
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)))
    else 0 := by
  have h := constituentCharacterCore_invariant_matching role size χ κ pivot n P hP
    childBound pivotBound ranges (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M l e hχ d d'
  dsimp only at h ⊢
  rw [constituentUnweighted_fourier_eq_grouped,
    constituentUnweighted_permuted_fourier_eq_grouped] at h
  split_ifs at h ⊢ with hp
  · exact h
  · simpa only [map_zero, zero_mul] using h

end Ostmann

end OAI
