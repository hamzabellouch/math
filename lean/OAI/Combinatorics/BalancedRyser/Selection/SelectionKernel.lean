import OAI.Combinatorics.BalancedRyser.Deletion.DeletionDomination
import OAI.Combinatorics.BalancedRyser.Selection.SelectionPushforward

namespace OAI

noncomputable section
namespace Balanced.DeletionLaw

def kernelOfSlotWeights {q n : ℕ}
    (w : Offset q n → Offset q n → ((Fin 2 × Fin n) → Fin q) → ℝ) : Weight q n :=
  fun m₀ m₁ s => w m₀ m₁ (fun t => s t.1 t.2)

end Balanced.DeletionLaw

end

end OAI
