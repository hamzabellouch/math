import OAI.Combinatorics.BalancedRyser.Deletion.Deletion
import OAI.Combinatorics.BalancedRyser.Incidence.Stability

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

def CorePencilResult : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ K : ℝ, 0 ≤ K → ∀ ζ : ℝ, 0 < ζ →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        Nat.Prime (Fintype.card F) →
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        ∀ Q : PMF (DeletionSet F k), DeletionDominated k K Q →
          deletionEventProbability Q (fun D => ¬ CorePencilEvent ζ D.val) < ε

end Balanced

end OAI
