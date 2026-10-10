import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealEndDescent

namespace OAI

/-! # A real logarithm of the square of a semisimple unit -/

noncomputable section
namespace PolycyclicRecognition

variable {n : ℕ}

def realSemisimpleSquareLog (S : Module.End ℝ (Fin n → ℝ)) (hS : S.IsSemisimple) :
    Module.End ℝ (Fin n → ℝ) :=
  complexEndRealPart n (semisimpleSquareLog (realEndComplexification n S)
    (realEndComplexification_semisimple n S hS))

theorem realSemisimpleSquareLog_complexify (S : Module.End ℝ (Fin n → ℝ))
    (hS : S.IsSemisimple) :
    realEndComplexification n (realSemisimpleSquareLog S hS) =
      semisimpleSquareLog (realEndComplexification n S)
        (realEndComplexification_semisimple n S hS) := by
  apply complexEndRealPart_descent
  intro x
  exact semisimpleSpectralOperator_conjugation _ _ (starLinearEquiv ℂ).toLinearMap
    (realEndComplexification_conj n S) complexSquareLog complexSquareLog_conj x

theorem exp_realSemisimpleSquareLog (S : Module.End ℝ (Fin n → ℝ))
    (hS : S.IsSemisimple) (hu : IsUnit S) :
    (NormedSpace.exp (LinearMap.toContinuousLinearMap
      (realSemisimpleSquareLog S hS))).toLinearMap = S ^ 2 := by
  apply realEndComplexification_injective n
  rw [realEndComplexification_exp, realSemisimpleSquareLog_complexify,
    exp_semisimpleSquareLog _ _ (hu.map (realEndComplexification n)), map_pow]

theorem realSemisimpleSquareLog_commute (S : Module.End ℝ (Fin n → ℝ))
    (hS : S.IsSemisimple) (T : Module.End ℝ (Fin n → ℝ)) (hc : Commute S T) :
    Commute (realSemisimpleSquareLog S hS) T := by
  apply realEndComplexification_injective n
  simp only [map_mul, realSemisimpleSquareLog_complexify, semisimpleSquareLog]
  exact (semisimpleSpectralOperator_commute _ _ complexSquareLog _
    (hc.map (realEndComplexification n))).eq

end PolycyclicRecognition

end

end OAI
