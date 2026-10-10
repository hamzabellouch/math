import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.Analysis.Laughlin.EnergyNonnegative

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem energy_eq_zero_iff {N Q : ℕ} (ψ : State N Q) :
    energy ψ = 0 ↔ ∀ (i j : Fin N), i < j → ∀ p : ℕ, p < 2*Q-1 →
      ∀ a : Configuration N Q, a i = 0 → a j = 0 → pairAmplitude ψ i j p a = 0 := by
  unfold energy
  simp (disch := intros; positivity) [Finset.sum_eq_zero_iff_of_nonneg]

end Laughlin

end OAI
