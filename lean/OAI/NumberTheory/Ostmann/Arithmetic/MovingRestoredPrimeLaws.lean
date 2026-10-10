import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitudeRestore
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredMultiplier

namespace OAI

/-! # The original prime sets and tiers in restored coordinates -/

namespace Ostmann
open scoped Classical

noncomputable def movingRestoredPrimeSets (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) : MovingRegularSlot n (4 + r) m → Finset ℕ :=
  fun i => Sum.elim (fun _ => Qμ) Qν ((movingReverseTemplate n r m).symm i)

noncomputable def movingRestoredTiers (n r m : ℕ)
    (tier : MovingRegularSlot n r m → ℕ) : MovingRegularSlot n (4 + r) m → ℕ :=
  fun i => Sum.elim (fun _ => n) tier ((movingReverseTemplate n r m).symm i)

@[simp] theorem movingRestoredPrimeSets_compensation (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) (i : TreeLeafIndex n × Fin 4) :
    movingRestoredPrimeSets n r m Qμ Qν (movingReverseTemplate n r m (.inl i)) = Qμ := by
  simp only [movingRestoredPrimeSets, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem movingRestoredPrimeSets_surviving (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) (i : MovingRegularSlot n r m) :
    movingRestoredPrimeSets n r m Qμ Qν (movingReverseTemplate n r m (.inr i)) = Qν i := by
  simp only [movingRestoredPrimeSets, Equiv.symm_apply_apply, Sum.elim_inr]

@[simp] theorem movingRestoredPrimeSets_bulk (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) (i : TreeLeafIndex n × Fin m) :
    movingRestoredPrimeSets n r m Qμ Qν (movingTemplateBulk n (4 + r) m i) =
      Qν (movingTemplateBulk n r m i) := by
  rw [← movingReverseTemplate_bulk, movingRestoredPrimeSets_surviving]

theorem movingRestoredPrimeSets_prior (P : Finset ℕ) (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ) :
    (fun i => primeSubsetPrior P (movingRestoredPrimeSets n r m Qμ Qν i)) =
      movingTemplateRestoredPrior n r m (primeSubsetPrior P Qμ) (fun i => primeSubsetPrior P (Qν i)) := by
  funext i a
  unfold movingTemplateRestoredPrior movingRestoredPrimeSets
  cases (movingReverseTemplate n r m).symm i <;> rfl

theorem movingRestoredTiers_lower (n r m : ℕ) (tier : MovingRegularSlot n r m → ℕ)
    (h : ∀ i, n ≤ tier i) : ∀ i, n ≤ movingRestoredTiers n r m tier i := by
  intro i
  unfold movingRestoredTiers
  cases (movingReverseTemplate n r m).symm i with
  | inl _ => exact le_rfl
  | inr j => exact h j

theorem movingRestoredPrimeSets_tier (P : Finset ℕ) (n r m : ℕ) (Qμ : Finset ℕ)
    (Qν : MovingRegularSlot n r m → Finset ℕ)
    (tier : MovingRegularSlot n r m → ℕ) (t : P → ℕ)
    (hμ : ∀ q : P, (q : ℕ) ∈ Qμ → t q = n)
    (hν : ∀ i (q : P), (q : ℕ) ∈ Qν i → t q = tier i) :
    ∀ i (q : P), (q : ℕ) ∈ movingRestoredPrimeSets n r m Qμ Qν i →
      t q = movingRestoredTiers n r m tier i := by
  intro i q
  unfold movingRestoredPrimeSets movingRestoredTiers
  cases (movingReverseTemplate n r m).symm i with
  | inl _ => exact hμ q
  | inr j => exact hν j q

end Ostmann

end OAI
