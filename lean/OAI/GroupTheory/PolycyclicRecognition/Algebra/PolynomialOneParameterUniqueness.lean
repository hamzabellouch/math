import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential
import OAI.GroupTheory.PolycyclicRecognition.Analysis.OneParameterIntegralCurve

namespace OAI

/-! # A smooth one-parameter subgroup is determined by its time-one value -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomial_oneParameter_eq_smul (γ : ℝ → L)
    (h0 : γ 0 = 1) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (hγ : ContDiff ℝ ∞ γ) (t : ℝ) : γ t = t • γ 1 := by
  have hd := ((hγ.differentiable (by simp)).differentiableAt (x := 0)).hasDerivAt
  have he (r : ℝ) : γ r = r • deriv γ 0 :=
    oneParameter_eq_groupExponential
      PolynomialExponentialCoordinates.isGroupExponential_identity h0 hmul
      (deriv γ 0) hd.hasFDerivAt.hasMFDerivAt r
  have h1 : γ 1 = deriv γ 0 := by simpa only [one_smul] using he 1
  rw [h1]
  exact he t

end PolycyclicRecognition

end

end OAI
