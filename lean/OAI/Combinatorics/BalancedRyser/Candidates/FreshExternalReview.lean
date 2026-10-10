import OAI.Combinatorics.BalancedRyser.Candidates.FreshExternalCounting
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessProbability

namespace OAI

noncomputable section
open scoped BigOperators
open _root_.Balanced _root_.OAI.Balanced Balanced.TupleAlignment

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

example (D : Finset (Direction F)) (a : MergedPairs F) :
    FreshWitnessProbability.exposedLaw D a = CandidateExposure.exposedLaw D a := by
  rfl

example (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (m : Nat) (hD : D.card ≤ m) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      FreshExternalWitness.probabilitySum g D a i j) ≤
        (5242880 * (m + 1)^4 : ℝ) :=
  FreshExternalWitness.all_positions_probabilitySum_le g D a m hD

example (g : Direction F) (a : MergedPairs F) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      FreshExternalWitness.probabilitySum g ∅ a i j) ≤ (5242880 : ℝ) := by
  simpa using FreshExternalWitness.all_positions_probabilitySum_le g ∅ a 0 (by simp)

end

end OAI
