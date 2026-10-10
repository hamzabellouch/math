import OAI.NumberTheory.Ostmann.Construction.ConstituentTransferWeight
import OAI.NumberTheory.Ostmann.Construction.ScheduledCurrentAmplitude

namespace OAI

/-! # The actual diagonal of the constituent-prime arithmetic step -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def constituentRetainedCoefficient {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  letI : ∀ h, Fact (a.1 h : ℕ).Prime := fun h => ⟨hP _ (a.1 h).property⟩
  letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  exact constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a *
    retainedPrimePhase (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) center
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph ρ initialCompleteGraph pivot n)
      (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) h.val (a.1 h))
      (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) y.val (u y)) M (frequencyRoot n (hist a.2))

noncomputable def constituentPivotDiagonal {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ) : ℂ :=
  pivotDiagonal (fun a => ∏ h, (a.1 h : ℕ)) (fun a => frequencyRoot n (hist a.2))
    (constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M)

end Ostmann

end OAI
