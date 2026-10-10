import OAI.NumberTheory.Ostmann.Construction.ConstituentPrimeGuardedAmplitude

namespace OAI

/-! # Restricting pivot tuples to the support of their original harmonic priors -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def supportedPivotTuples (P : Finset ℕ) {r : ℕ}
    (Q : Fin r → Finset ℕ) : Finset (Fin r → P) :=
  (Finset.univ.filter Function.Injective).filter (fun x => ∀ i, (x i : ℕ) ∈ Q i)

theorem mem_supportedPivotTuples (P : Finset ℕ) {r : ℕ} (Q : Fin r → Finset ℕ) (x : Fin r → P) :
    x ∈ supportedPivotTuples P Q ↔ Function.Injective x ∧ ∀ i, (x i : ℕ) ∈ Q i := by
  simp only [supportedPivotTuples, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Zero prior mass permits the exact restriction to the original prime cells. -/
theorem scheduledCurrentAmplitude_restrict_cells {I A Z : Type*}
    [Fintype I] [Fintype A] [Fintype Z]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (hist : A → FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : Fin r → Finset ℕ) (S : Finset (Fin r → P))
    (L : A → CopyScheduleH role n → ℕ) (U : Z → CopyScheduleY role n → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ z y, Fact (U z y).Prime]
    (center : ∀ p : ℕ, ZMod p) (W : Z → ℕ → A → ℂ) (μ : Z → ℝ) :
    scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q S L U center W μ =
      scheduledCurrentAmplitude role χ κ pivot n r e hist P hP Q
        (S.filter (fun x => ∀ i, (x i : ℕ) ∈ Q i)) L U center W μ := by
  unfold scheduledCurrentAmplitude
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hq : ∀ i, (x i : ℕ) ∈ Q i
  · rw [ite_eq_left hq]
  · rw [ite_eq_right hq]
    have hz : productPrior (fun i => primeSubsetPrior P (Q i)) x = 0 := by
      by_contra hn
      apply hq
      intro i
      exact primeSubsetPrior_support P (Q i) (x i)
        ((Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i))
    simp only [hz, Complex.ofReal_zero, zero_mul]

theorem constituentPrimeGuardedAmplitude_eq_supported_transfer {I D : Type*}
    [Fintype I] [Fintype D]
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
    constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center =
      scheduledCurrentAmplitude ρ χ κ pivot n (size p) (pivotConstituentEquiv role size n p hp hu)
        (fun a => hist a.2) P hP (fun k => Q ⟨p, k⟩) (supportedPivotTuples P (fun k => Q ⟨p, k⟩))
        (fun a h => (a.1 h : ℕ)) (fun u y => (u y : ℕ)) center
        (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist)
        (fun u => ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let : ∀ (a : (CopyScheduleH ρ n → P) × D) h, Fact (a.1 h : ℕ).Prime :=
    fun a h => ⟨hP _ (a.1 h).property⟩
  let : ∀ (u : CopyScheduleY ρ n → P) y, Fact (u y : ℕ).Prime :=
    fun u y => ⟨hP _ (u y).property⟩
  rw [constituentPrimeGuardedAmplitude_eq_transfer role size χ κ pivot n p hp hu]
  apply scheduledCurrentAmplitude_restrict_cells

end Ostmann

end OAI
