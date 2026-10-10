import OAI.Combinatorics.EditApproximation.Binary.BinarySampledOnline

namespace OAI

/-! Cost of the actual triangular choice followed by the complete stored
fraction online optimizer. This includes the envelope and vertex builders. -/

namespace EditApproximation
namespace BinaryFraction

theorem sampledOnlineActionWithWork_cost {ny M : ℕ} (center : TargetInterval ny) (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K))
    (B Be Bk Bi Bt E : ℕ) (hb : 0 < b) (hM : 0 < M)
    (hK : Nat.size K ≤ B) (hinteger : Nat.size integer.val ≤ B)
    (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
    (hi : ∀ action ∈ band, ∀ j, (initial j (action j)).width ≤ Bi)
    (ht : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (table s ((listedBandCoordinateVector band).get i)).width ≤ Bt)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (htrange : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      0 ≤ (table s ((listedBandCoordinateVector band).get i)).value ∧
        (table s ((listedBandCoordinateVector band).get i)).value ≤
          (initial ((listedBandCoordinateVector band).get i).1
            ((listedBandCoordinateVector band).get i).2).value) :
    (sampledOnlineActionWithWork center b initial table eta kappa band hne G K t integer).2 ≤
      triangularChoiceBitBudget K B +
      bandActionBitBudget M (listedBandCoordinates band).length b band.length G
        (triangularChoice K integer).val t Be Bk Bi Bt E + M + 2 := by
  have hchoice := triangularChoiceWithWork_cost K integer B hK hinteger
  have hoptimizer := bandActionWithWork_cost b initial table eta kappa band G
    (triangularChoice K integer).val t Be Bk Bi Bt E hne hb hM he hk hi ht heabs hkrange htrange
  unfold sampledOnlineActionWithWork
  dsimp only
  rw [triangularChoiceWithWork_value]
  omega

end BinaryFraction
end EditApproximation

end OAI
