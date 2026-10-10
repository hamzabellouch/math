import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.GradientRieszTestIdentity
import OAI.Analysis.RieszRectifiability.Limits.CompactDerivativeTests

namespace OAI

/-!
# The fractional equation from density Riesz tests

Summing the vanishing Riesz pairings against directional derivatives over an
orthonormal basis gives the fractional Schwartz equation. The finite sum also
supplies integrability, with the factor `-1 / 2` fixed by the gradient identity.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology

theorem density_fractional_equation_of_riesz_tests (p : ℕ)
    (f : Ambient (p + 1) → ℝ) (ψ : 𝓢(Ambient (p + 1), ℝ))
    (hEq : ∀ e : Ambient (p + 1),
      Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e (scalarSchwartzDerivative ψ e) y) volume ∧
        (∫ y, f y * scalarRieszSchwartzTest (p + 1) e (scalarSchwartzDerivative ψ e) y) = 0) :
    Integrable (fun y => f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0 := by
  let b := EuclideanSpace.basisFun (Fin (p + 1)) ℝ
  let F : Fin (p + 1) → Ambient (p + 1) → ℝ := fun i y =>
    f y * scalarRieszSchwartzTest (p + 1) (b i) (scalarSchwartzDerivative ψ (b i)) y
  have hI (i : Fin (p + 1)) : Integrable (F i) volume := (hEq (b i)).1
  have heq : (fun y => f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) =
      fun y => ∑ i, F i y := by
    funext y
    dsimp only [F]
    rw [← Finset.mul_sum]
    exact congrArg (fun z : ℝ => f y * z) (sum_scalarRieszSchwartzTest_gradient p b ψ y).symm
  rw [heq]
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hI i), ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => hI i)]
  exact Finset.sum_eq_zero fun i _ => (hEq (b i)).2

end

end RieszRectifiability

end OAI
