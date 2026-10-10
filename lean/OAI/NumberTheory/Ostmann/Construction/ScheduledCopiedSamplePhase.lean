import OAI.NumberTheory.Ostmann.Construction.ScheduledSamplePhase
import OAI.NumberTheory.Ostmann.Construction.ConstituentCopiedAmplitude

namespace OAI

/-! # The copied arithmetic phase is the next finite-sample phase -/

namespace Ostmann

open scoped Classical

theorem scheduledSamplePhase_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : CopyScheduleY role n → P) (l r : CopyScheduleH role n → P)
    (center : ∀ p : ℕ, ZMod p) :
    letI : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
    letI : ∀ h, Fact (r h : ℕ).Prime := fun h => ⟨hP _ (r h).property⟩
    letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
    letI := transferredPrimeFact (fun h => (l h : ℕ)) (fun h => (r h : ℕ)) (fun y => (u y : ℕ))
    scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ) (n + 1) t
      (fun i => transferredLabels (fun h => (l h : ℕ)) (fun h => (r h : ℕ)) (fun y => (u y : ℕ))
        (copyScheduleSurvivorEquiv role n i)) center =
    scheduledSamplePhase role χ κ pivot (n + 1) t P hP (scheduledCopiedAssignment role n u l r) center := by
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ h, Fact (r h : ℕ).Prime := fun h => ⟨hP _ (r h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  let := transferredPrimeFact (fun h => (l h : ℕ)) (fun h => (r h : ℕ)) (fun y => (u y : ℕ))
  let : ∀ i, Fact ((scheduledCopiedAssignment role n u l r i : P) : ℕ).Prime :=
    fun i => ⟨hP _ (scheduledCopiedAssignment role n u l r i).property⟩
  unfold scheduledSamplePhase
  apply scheduledPrimePhase_congr_labels
  funext i
  unfold scheduledCopiedAssignment
  generalize copyScheduleSurvivorEquiv role n i = j
  rcases j with ⟨b, h⟩ | y
  · cases b <;> rfl
  · rfl

end Ostmann

end OAI
