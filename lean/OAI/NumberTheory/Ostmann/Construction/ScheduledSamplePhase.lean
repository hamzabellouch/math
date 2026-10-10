import OAI.NumberTheory.Ostmann.Construction.ScheduledCurrentAmplitude
import OAI.NumberTheory.Ostmann.Construction.ConstituentPriorAssembly

namespace OAI

/-! # The actual scheduled phase on a finite prime sample -/

namespace Ostmann

open scoped Classical

theorem scheduledPrimePhase_congr_labels {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ n)
    (p q : CopyScheduleAtoms role n → ℕ) [∀ i, Fact (p i).Prime] [∀ i, Fact (q i).Prime]
    (center : ∀ p : ℕ, ZMod p) (h : p = q) :
    scheduledPrimePhase role χ g pivot initial n t p center =
      scheduledPrimePhase role χ g pivot initial n t q center := by
  subst q
  rfl

noncomputable def scheduledSamplePhase {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n : ℕ) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (q : CopyScheduleAtoms role n → P)
    (center : ∀ p : ℕ, ZMod p) : ℂ := by
  letI : ∀ i, Fact (q i : ℕ).Prime := fun i => ⟨hP _ (q i).property⟩
  exact scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ)
    n t (fun i => (q i : ℕ)) center

/-- Finite Fubini and the arithmetic transfer evaluate literally the same
scheduled phase after the pivot/H/Y reindexing. -/
theorem scheduledSamplePhase_partition {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n r : ℕ)
    (e : Fin r ≃ CurrentPivotConstituent role n) (t : FrequencyTree ℤ n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : CopyScheduleY role n → P) (x : Fin r → P) (l : CopyScheduleH role n → P)
    (center : ∀ p : ℕ, ZMod p) :
    letI : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
    letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
    scheduledSamplePhase role χ κ pivot n t P hP
        (scheduledPartitionAssignment role n r e u x l) center =
      sampledScheduledPhase role χ κ pivot n r e t P hP x
        (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) center := by
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  let : ∀ k, Fact (x k : ℕ).Prime := fun k => ⟨hP _ (x k).property⟩
  let := scheduledInputPrimeFact role n r e (fun k => (x k : ℕ))
    (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
  let : ∀ i, Fact ((scheduledPartitionAssignment (A := P) role n r e u x l i : P) : ℕ).Prime :=
    fun i => ⟨hP _ (scheduledPartitionAssignment role n r e u x l i).property⟩
  unfold scheduledSamplePhase sampledScheduledPhase
  apply scheduledPrimePhase_congr_labels
  exact scheduledPartitionAssignment_map role n r e (fun q : P => (q : ℕ)) u x l

end Ostmann

end OAI
