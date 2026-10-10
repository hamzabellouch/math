import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkMean

namespace OAI

/-! # Retaining factors independent of the selected bulk draws -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternBulkMean_weight {A B C : Type*} [Fintype A] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (ν : B → A → ℝ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (W G : (Fin (N + 1) → A) → ℂ)
    (hW : ∀ x z, W (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i)) = W x)
    (x : Fin (N + 1) → A) :
    movingPatternBulkMean e ν slot (fun x => W x * G x) x =
      W x * movingPatternBulkMean e ν slot G x := by
  unfold movingPatternBulkMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  rw [hW x z]
  ring

end Ostmann

end OAI
