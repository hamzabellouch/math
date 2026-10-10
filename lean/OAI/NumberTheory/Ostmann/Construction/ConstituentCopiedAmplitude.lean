import OAI.NumberTheory.Ostmann.Construction.ConstituentOriginalAmplitude

namespace OAI

/-! # Reassembling the next full amplitude with its unchanged original priors -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduledCopiedAssignment_map {I A B : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) (f : A → B)
    (u : CopyScheduleY role n → A) (l r : CopyScheduleH role n → A) :
    (fun i => f (scheduledCopiedAssignment role n u l r i)) =
      scheduledCopiedAssignment role n (f ∘ u) (f ∘ l) (f ∘ r) := by
  funext i
  obtain ⟨j, rfl⟩ := (copyScheduleSurvivorEquiv role n).symm.surjective i
  rcases j with ⟨b, h⟩ | y
  · cases b <;> rfl
  · rfl

/-- The next global amplitude has exactly the two H priors and one Y prior
appearing after arithmetic transfer. All Fourier and arithmetic support stays
inside the same full coefficient. -/
theorem constituentOriginalAmplitude_copied {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ (n + 1))
    (center : ∀ p : ℕ, ZMod p) :
    constituentOriginalAmplitude role size χ κ pivot (n + 1) P hP Q
      childBound pivotBound ranges leaf hist center =
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    ∑ u : CopyScheduleY ρ n → P,
      ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
      ∑ l : CopyScheduleH ρ n → P,
        ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h) : ℝ) : ℂ) *
        ∑ r : CopyScheduleH ρ n → P,
          ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h) : ℝ) : ℂ) *
          ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
            (scheduledCopiedAssignment role n
              (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))
              (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
              (fun h => ∏ k, (r (constituentH role size n h k) : ℕ))) (hist d) *
            scheduledSamplePhase ρ χ κ pivot (n + 1) (hist d) P hP
              (scheduledCopiedAssignment ρ n u l r) center := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  have hF := copied_prior_fubini ρ n
    (scheduledRolePrior ρ (fun j => primeSubsetPrior P (Q j)) (n + 1))
    (fun q => ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
      (fun v => ((scheduleConstituentWord role size (n + 1) v).map (fun i => (q i : ℕ))).prod)
      (hist d) * scheduledSamplePhase ρ χ κ pivot (n + 1) (hist d) P hP q center)
  change constituentOriginalAmplitude role size χ κ pivot (n + 1) P hP Q
    childBound pivotBound ranges leaf hist center = _ at hF
  refine hF.trans ?_
  simp only [scheduledRolePrior_copied]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  have hmap := scheduledCopiedAssignment_map ρ n (fun q : P => (q : ℕ)) u l r
  have hg := constituent_copied_assignment role size n
    (fun y => (u y : ℕ)) (fun h => (l h : ℕ)) (fun h => (r h : ℕ))
  have hg' : (fun v => ((scheduleConstituentWord role size (n + 1) v).map
      (fun i => ((scheduledCopiedAssignment (A := P) ρ n u l r i : P) : ℕ))).prod) =
      scheduledCopiedAssignment role n
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))
        (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
        (fun h => ∏ k, (r (constituentH role size n h k) : ℕ)) := by
    rw [hmap]
    exact hg
  rw [hg']

end Ostmann

end OAI
