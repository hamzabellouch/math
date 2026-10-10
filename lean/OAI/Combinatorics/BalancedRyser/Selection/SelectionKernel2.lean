import OAI.Combinatorics.BalancedRyser.Selection.SelectionKernel
import OAI.Combinatorics.BalancedRyser.Selection.SelectionPushforward2

namespace OAI

namespace Balanced.DeletionLaw

theorem sum_kernelOfSlotWeights {q n : ℕ}
    (w : Offset q n → Offset q n → ((Fin 2 × Fin n) → Fin q) → ℝ)
    (m₀ m₁ : Offset q n) :
    ∑ s, kernelOfSlotWeights w m₀ m₁ s = ∑ t, w m₀ m₁ t := by
  exact Fintype.sum_equiv (Equiv.curry (Fin 2) (Fin n) (Fin q)).symm
    (fun s => kernelOfSlotWeights w m₀ m₁ s) (w m₀ m₁) (fun _ => rfl)

theorem kernelOfSlotWeights_subprobability {q n : ℕ}
    (w : Offset q n → Offset q n → ((Fin 2 × Fin n) → Fin q) → ℝ)
    (hw : ∀ m₀ m₁ t, 0 ≤ w m₀ m₁ t)
    (hmass : ∀ m₀ m₁, ∑ t, w m₀ m₁ t ≤ 1) :
    IsSubprobabilityKernel (kernelOfSlotWeights w) := by
  constructor
  · intro m₀ m₁ s
    exact hw m₀ m₁ _
  · intro m₀ m₁
    rw [sum_kernelOfSlotWeights]
    exact hmass m₀ m₁

theorem kernelOfSlotWeights_cylinders {q n : ℕ}
    (w : Offset q n → Offset q n → ((Fin 2 × Fin n) → Fin q) → ℝ) (K : ℝ)
    (hbound : ∀ m₀ m₁ J t,
      FinitePushforward.cylinderMass (w m₀ m₁) J t ≤ (K / q) ^ J.card) :
    CylinderBound (kernelOfSlotWeights w) K := by
  intro m₀ m₁ J t
  calc
    (∑ s, if ∀ j ∈ J, s j.1 j.2 = t j then kernelOfSlotWeights w m₀ m₁ s else 0) =
        FinitePushforward.cylinderMass (w m₀ m₁) J t := by
      exact Fintype.sum_equiv (Equiv.curry (Fin 2) (Fin n) (Fin q)).symm
        _ _ (fun _ => rfl)
    _ ≤ (K / q) ^ J.card := hbound m₀ m₁ J t

end Balanced.DeletionLaw

end OAI
