import OAI.Combinatorics.EditApproximation.Binary.BinaryCountedActionSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryTriangularSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction

/-- Concrete allocated cells of the sampled labeled online action, including
threshold search, envelopes, coordinate arrays and all optimizer arithmetic. -/


theorem countedSampledOnlineAllocation_le_work {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (initialAllocation : Fin M → TargetInterval n → ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (readAllocation : ℕ → Fin M × TargetInterval n → ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hi : ∀ i state, initialAllocation i state ≤ (initial i state).2)
    (hr : ∀ s coordinate, readAllocation s coordinate ≤ (read s coordinate).2) :
    countedSampledOnlineAllocation center b initial initialAllocation read readAllocation eta kappa band hne
      G K t integer ≤ 3 * (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).2 := by
  have ht := triangularChoiceAllocation_le_work K integer
  have ha := countedBandActionAllocation_le_work b initial initialAllocation read readAllocation
    eta kappa band G (triangularChoiceWithWork K integer).1.val t hi hr
  unfold countedSampledOnlineAllocation countedSampledOnlineReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
