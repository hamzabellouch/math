import Mathlib
import OAI.Analysis.Conductivity.Scalarization.SmoothScalarAlgebra

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def twoFluxDivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (F : Fin 5 → SmoothScalar E) : Fin 2 → SmoothScalar E :=
  ![smoothDirection (v 0) (F 0) + smoothDirection (v 1) (F 1) +
      smoothDirection (v 2) (F 3),
    smoothDirection (v 0) (F 1) + smoothDirection (v 1) (F 2) +
      smoothDirection (v 2) (F 4)]

def airyFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (φ : SmoothScalar E) : Fin 5 → SmoothScalar E :=
  ![smoothDirection (v 1) (smoothDirection (v 1) φ),
    -(smoothDirection (v 0) (smoothDirection (v 1) φ)),
    smoothDirection (v 0) (smoothDirection (v 0) φ), 0, 0]

def transverseFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (ψ η ω : SmoothScalar E) : Fin 5 → SmoothScalar E :=
  ![smoothDirection (v 2) ψ, smoothDirection (v 2) η, smoothDirection (v 2) ω,
    -(smoothDirection (v 0) ψ) - smoothDirection (v 1) η,
    -(smoothDirection (v 0) η) - smoothDirection (v 1) ω]

theorem airyFlux_divergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (φ : SmoothScalar E) :
    twoFluxDivergence v (airyFlux v φ) = 0 := by
  have h01 := smoothDirection_comm (v 0) (v 1)
  funext i
  fin_cases i <;> simp [twoFluxDivergence, airyFlux, h01]

theorem transverseFlux_divergence {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : Fin 3 → E) (ψ η ω : SmoothScalar E) :
    twoFluxDivergence v (transverseFlux v ψ η ω) = 0 := by
  have h02 := smoothDirection_comm (v 0) (v 2)
  have h12 := smoothDirection_comm (v 1) (v 2)
  funext i
  fin_cases i <;> simp [twoFluxDivergence, transverseFlux, h02, h12]

end ScalarConductivity

end

end OAI
