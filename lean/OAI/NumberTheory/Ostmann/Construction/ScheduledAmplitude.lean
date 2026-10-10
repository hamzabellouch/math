import OAI.NumberTheory.Ostmann.Construction.InitialScheduledAmplitude
import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedCompensationPrior

namespace OAI

/-! # Actual amplitudes along the shrinking compensation list -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def scheduledCellAmplitude {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) : ℂ :=
  movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G
    n (scheduledSmallLength (cs.drop n)) m Pg ρ
    (scheduledRegularPrior cell bulk top (cs.drop n) n m) greg ggiant favorable

theorem scheduledCellAmplitude_restore {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool)
    (hn : n < cs.length) (hμ : μ n = cell ((cs.drop n).headD 0)) :
    let r := scheduledSmallLength (cs.drop (n + 1))
    let ν := scheduledRegularPrior cell bulk top (cs.drop (n + 1)) n m
    scheduledCellAmplitude value outside μ childBound pivotBound V F φ G Pg ρ
      cell bulk top cs n m greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
      Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable := by
  intro r ν
  unfold scheduledCellAmplitude
  conv_lhs => rw [drop_eq_headD_cons cs 0 n hn, scheduledRegularPrior_restore]
  rw [hμ]
  rfl

theorem scheduledCellAmplitude_next {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    let r := scheduledSmallLength (cs.drop (n + 1))
    let ν := scheduledRegularPrior cell bulk top (cs.drop (n + 1)) n m
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
      Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable =
    scheduledCellAmplitude value outside μ childBound pivotBound V F φ G Pg ρ
      cell bulk top cs (n + 1) m greg ggiant favorable := rfl

theorem completedCompensationPrior_cell (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) (hn : n < cs.length) :
    completedCompensationPrior A B N X hi D P top cs n =
      primeSubsetPrior P (selectedTailCellPrimes A B N X hi D ((cs.drop n).headD 0)) := by
  exact completedCompensationPrior_used A B N X hi D P top cs n hn

end Ostmann

end OAI
