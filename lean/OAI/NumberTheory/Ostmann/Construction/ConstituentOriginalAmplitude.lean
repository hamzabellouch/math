import OAI.NumberTheory.Ostmann.Construction.ScheduledSamplePhase
import OAI.NumberTheory.Ostmann.Construction.ScheduledRolePrior

namespace OAI

/-! # The actual original-prior amplitude in arithmetic-transfer coordinates -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def constituentOriginalAmplitude {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) : ℂ :=
  ∑ q : SurvivingConstituent role size n → P,
    ((∏ i, scheduledRolePrior (fun i : Σ a, Fin (size a) => role i.1)
      (fun j => primeSubsetPrior P (Q j)) n i (q i) : ℝ) : ℂ) *
    ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod)
      (hist d) * scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1)
        χ κ pivot n (hist d) P hP q center

noncomputable def constituentCurrentWeight {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ :=
  ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (a.1 h) : ℝ) : ℂ) *
    fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, (a.1 (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist a.2)

/-- This identifies the full original-prior expectation, including its actual
phase and every history guard, with the amplitude in the proved arithmetic step. -/
theorem constituentOriginalAmplitude_eq_current {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    letI : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
      fun a h => ⟨hP _ (a.1 h).property⟩
    letI : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
      fun u y => ⟨hP _ (u y).property⟩
    constituentOriginalAmplitude role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center =
      scheduledCurrentAmplitude ρ χ κ pivot n (size p) (pivotConstituentEquiv role size n p hp hu)
        (fun a => hist a.2) P hP (fun k => Q ⟨p, k⟩) Finset.univ
        (fun a h => (a.1 h : ℕ)) (fun u y => (u y : ℕ)) center
        (constituentCurrentWeight role size n P Q childBound pivotBound ranges leaf hist)
        (fun u => ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  have hF := constituent_weighted_prior_fubini role size n p hp hu P
    (scheduledRolePrior ρ (fun j => primeSubsetPrior P (Q j)) n)
    childBound pivotBound ranges leaf hist
    (fun q d => scheduledSamplePhase ρ χ κ pivot n (hist d) P hP q center)
  change constituentOriginalAmplitude role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist center = _ at hF
  refine hF.trans ?_
  simp only [scheduledRolePrior, enumeratedPartitionEquiv_pivot,
    enumeratedPartitionEquiv_rest, copyScheduleOrigin_positive, Sum.elim_inl, Sum.elim_inr]
  unfold scheduledCurrentAmplitude constituentCurrentWeight productPrior
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro d _
  dsimp only [ρ]
  rw [scheduledSamplePhase_partition]
  have hq (k) : Q (pivotConstituentEquiv role size n p hp hu k).val = Q ⟨p, k⟩ := rfl
  simp_rw [hq]
  ring

end Ostmann

end OAI
