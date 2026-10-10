import OAI.Analysis.KadisonKastler.GaussianStateAverage
import OAI.Analysis.KadisonKastler.GaussianVectorAnalytic

namespace OAI

/-! # Entire coefficients of the concrete Gaussian operator average -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_vector_differentiable
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (x : H) :
    Differentiable ℂ (fun z : ℂ => gaussianStateAverage U hU a r hr z x) := by
  apply gaussianVector_differentiable
    (fun t => stateActionOrbit U a t x) (stateActionOrbit_continuous U hU a x)
    (‖a‖ * ‖x‖) ?_ r hr
  intro t
  exact ((stateActionOrbit U a t).le_opNorm x).trans_eq (by rw [stateActionOrbit_norm])

theorem gaussianStateAverage_coefficient_differentiable
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (x y : H) :
    Differentiable ℂ (fun z : ℂ => inner ℂ y (gaussianStateAverage U hU a r hr z x)) :=
  (innerSL ℂ y).differentiable.comp (gaussianStateAverage_vector_differentiable U hU a r hr x)

end

end KadisonKastler

end OAI
