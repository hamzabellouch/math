import Mathlib
import OAI.Probability.SKValue.Gaussian.IntegralPositiveMulGaussian
import OAI.Probability.SKValue.Processes.TestExpectation
import OAI.Probability.SKValue.Processes.ForcedExpectation
import OAI.Probability.SKValue.Processes.ForcedDiffusion
import OAI.Probability.SKValue.Equations.PolynomialForced
import OAI.Probability.SKValue.Evolution.HeatConvexity
import OAI.Probability.SKValue.Evolution.TerminalAlgebra
import OAI.Probability.SKValue.Evolution.TestStrip
import OAI.Probability.SKValue.GroundState.MainConclusions

namespace OAI

namespace SKValue

theorem value_consequences :
    (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ),
      IsMinimizer W γ → IsDiffusion W γ X → ScalarValueConclusion W γ X) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ) (T : ℝ),
      0 < T → T < 1 → IsMinimizer W γ → IsDiffusion W γ X →
      FiniteGaussianConclusion W γ X T) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter),
      IsMinimizer W γ → groundStateValue = parisi W γ) := by
  exact ⟨scalar_value_target, finite_gaussian_target, ground_state_parisi_target⟩

end SKValue

end OAI
