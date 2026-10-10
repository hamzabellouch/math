import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchedCharacter
import OAI.NumberTheory.Ostmann.Construction.InsertedConstituentFourier

namespace OAI

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem constituentCharacterCore_pair_fourier {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hist : D → FrequencyTree ℤ n)
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
        childBound pivotBound ranges (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M (l, d) *
      conj (constituentCharacterCore role size (fun _ => χ) κ pivot n P hP
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
    finiteEdgeWeight (dirichletGraphEdge (fun _ => χ)
      (graphDifference (retainedInternalGraph g) (transportGraph σ (retainedInternalGraph g))))
      (fun i x => externalPivotUnary (fun _ => χ) g ν M i x *
        conj (externalPivotUnary (fun _ => χ) g ω M (σ.symm i) x))
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)))
    else 0 := by
  have h := constituentCharacterCore_common_matching role size χ κ pivot n P hP
    childBound pivotBound ranges (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M l e d d'
  dsimp only at h ⊢
  rw [constituentUnweighted_fourier_eq_grouped,
    constituentUnweighted_permuted_fourier_eq_grouped] at h
  split_ifs at h ⊢ with hp
  · exact h
  · simpa only [map_zero, zero_mul] using h

end Ostmann

end OAI
