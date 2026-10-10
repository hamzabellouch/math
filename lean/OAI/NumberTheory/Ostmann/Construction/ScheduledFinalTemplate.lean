import OAI.NumberTheory.Ostmann.Construction.ScheduledAmplitude

namespace OAI

/-! # The last stage retains exactly the six original top-cell copies -/
namespace Ostmann
open scoped Classical BigOperators

theorem scheduledRegularPrior_nil {A : Type} (cell : ℕ → A → ℝ)
    (bulk : A → ℝ) (top n m : ℕ) :
    scheduledRegularPrior cell bulk top [] n m =
      fun i => Sum.elim (fun _ => cell top) (fun _ => bulk) i.2 := rfl

theorem scheduledCellAmplitude_final {A : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState A → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (k m : ℕ)
    (hlen : cs.length = k)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    scheduledCellAmplitude value outside μ childBound pivotBound V F φ G Pg ρ
      cell bulk top cs k m greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G k 6 m Pg ρ
      (fun i => Sum.elim (fun _ => cell top) (fun _ => bulk) i.2) greg ggiant favorable := by
  have hdrop : cs.drop k = [] := by rw [← hlen, List.drop_length]
  unfold scheduledCellAmplitude
  rw [hdrop]
  rfl

theorem scheduled_final_length (top : ℕ) (cs : List ℕ) (k : ℕ) (hlen : cs.length = k) :
    6 + 4 * k = (initialSmallCellList top cs).length + (initialSmallCellList top cs).length := by
  simp only [initialSmallCellList_length, hlen]
  omega

end Ostmann

end OAI
