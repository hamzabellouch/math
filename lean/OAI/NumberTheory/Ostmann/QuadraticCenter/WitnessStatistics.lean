import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessArraySplit
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessLiftCount
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessProbability

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter

def primeProductSmallOffEventNorm (L : ℕ) [NeZero L]
    (A : ∀p:ℕ,Finset (ZMod p)) (lam X K : ℝ) (t : ℕ→ℤ) (q : ℕ) : ℝ := by
  classical
  exact if primeProductWitness L A X K t q then 0 else
    ‖primeProductSmallSum L A lam X t q‖

theorem quadraticWitnessProducts_probability (L : ℕ) [NeZero L]
    (A : ∀p:ℕ,Finset (ZMod p)) (X K : ℝ) (t : ℕ→ℤ) (P : Finset ℕ) (k : ℕ) :
    (quadraticWitnessProducts P k L A X K t).card / (Nat.choose P.card k:ℝ) =
      @primeProductProbability P k (primeProductWitness L A X K t) (Classical.decPred _) := by
  classical
  exact (primeProductProbability_eq_card P k (primeProductWitness L A X K t)).symm

end Ostmann.QuadraticCenter

end

end OAI
