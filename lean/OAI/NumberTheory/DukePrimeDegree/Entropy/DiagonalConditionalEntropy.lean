import OAI.NumberTheory.PrimePackets.FutureConditionalEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.DiagonalEntropy

namespace OAI

/-!
# Actual diagonal entropy as conditional information

Finite-observation entropy on the arithmetic lattice quotient is the
conditional information of the present given the complete future.
The conditional expectations are defined independently of root coefficients.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonalOneParameter_measurePreserving (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X (d+1)))
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (t : ℝ) :
    MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell t)) μ μ := by
  refine ⟨(continuous_rightAction _).measurable, ?_⟩
  rw [diagonalOneParameter_eq_diagonalFlow]
  exact hA _

theorem diagonal_entropy_eq_futureConditionals (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (t : ℝ) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t)) =
      ⨆ k, ENNReal.ofReal
        (conditionalSigmaEntropy μ (finiteGeneratingObservation (X (d+1)) k)
          (⨆ n, observationSigma
            (futureName (fun x => rightAction x (diagonalOneParameter ell hell t))
              (finiteGeneratingObservation (X (d+1)) k) n))) :=
  measureEntropy_eq_iSup_futureConditional μ
    (diagonalOneParameter_measurePreserving d ell hell μ hA t)

end DukePrimeDegree

end

end OAI
