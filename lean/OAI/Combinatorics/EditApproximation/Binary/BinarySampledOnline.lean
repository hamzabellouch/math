import OAI.Combinatorics.EditApproximation.Binary.BinaryTriangularChoice
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandAction
import OAI.Combinatorics.EditApproximation.Binary.BinaryPhysicalContinuation

namespace OAI

/-! A finite uniform source integer is passed through the actual triangular
search and the actual stored-fraction optimizer. The returned zero-connection
physical action has exactly the online sampler's value, including ties. -/

namespace EditApproximation
namespace BinaryFraction

def sampledOnlineActionWithWork {ny M : ℕ} (center : TargetInterval ny) (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M × ℕ :=
  let chosen := triangularChoiceWithWork K integer
  let selected := bandActionWithWork b initial table eta kappa band G chosen.1.val t
  let states := selected.1.getD (band.head hne)
  (⟨center, zero, fun i => (i, states i)⟩, chosen.2 + selected.2 + M + 2)

theorem sampledOnlineActionWithWork_value {ny M : ℕ} (center : TargetInterval ny) (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) (hb : 0 < b) :
    (sampledOnlineActionWithWork center b initial table eta kappa band hne G K t integer).1.decode =
      sharedBandRationalAction center
        (finiteOptimizerActionDraw band hne (bandChildEnvelope b band (fun i q => (initial i q).value))
          (rationalOnlineLinear eta.value kappa.value
            (childGain (bandChildEnvelope b band (fun i q => (initial i q).value))
              (fun s i => (table s i).value))
            (childDecrement (bandChildEnvelope b band (fun i q => (initial i q).value))
              (fun s i => (table s i).value)) t) G K integer) := by
  simp only [sampledOnlineActionWithWork, BinaryBellmanAction.decode,
    bandActionWithWork_value _ _ _ _ _ _ hne _ _ _ hb, triangularChoiceWithWork_value,
    finiteOptimizerActionDraw, sharedBandRationalAction]
  rw [← representation_value zero, zero_representation, UnreducedRational.value_zero]

end BinaryFraction
end EditApproximation

end OAI
