import Mathlib
import OAI.Probability.SKValue.Variation.MinimizerContact
import OAI.Probability.SKValue.Variation.ContactAssembly
import OAI.Probability.SKValue.Processes.DiffusionExistence

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue

theorem scalar_value_target (W:BrownianSpace) (γ:OrderParameter) (X:ℝ → W.Ω → ℝ)
    (hmin:IsMinimizer W γ) (hX:IsDiffusion W γ X):ScalarValueConclusion W γ X :=
  hX.scalar_value_of_contact (hmin.gradient_moment_contact hX)

theorem finite_gaussian_target (W:BrownianSpace) (γ:OrderParameter) (X:ℝ → W.Ω → ℝ)
    (T:ℝ) (hT:0<T) (hT1:T<1) (hmin:IsMinimizer W γ) (hX:IsDiffusion W γ X):
    FiniteGaussianConclusion W γ X T :=
  hX.finite_gaussian_of_contact (hmin.gradient_moment_contact hX) hT hT1
lemma IsMinimizer.ground_state_parisi_of_diffusion {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hmin:IsMinimizer W γ) (hX:IsDiffusion W γ X):groundStateValue=parisi W γ :=
  hX.groundState_eq_parisi_of_contact (hmin.gradient_moment_contact hX)

theorem ground_state_parisi_target (W:BrownianSpace) (γ:OrderParameter)
    (hmin:IsMinimizer W γ):groundStateValue=parisi W γ :=
  hmin.ground_state_parisi_of_diffusion (diffusionProcess_isDiffusion W γ)
end SKValue

end

end OAI
