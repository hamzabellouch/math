import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.SobolevSpace

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def schwartzToH (s : ℝ) : 𝓢(E,F) →L[ℂ] H E F s :=
  (SchwartzMap.toLpCLM ℂ F 2 (volume : Measure E)).comp
    (SchwartzMap.fourierMultiplierCLM F (fun x : E => ((1+‖x‖^2)^(s/2) : ℝ)))

lemma schwartzToH_spec (s : ℝ) (f : 𝓢(E,F)) :
    toDistribution E F s (schwartzToH s f) = (f : 𝓢'(E,F)) := by
  rw [toDistribution,ContinuousLinearMap.comp_apply,schwartzToH,
    ContinuousLinearMap.comp_apply,SchwartzMap.toLpCLM_apply,
    Lp.toTemperedDistributionCLM_apply]
  rw [besselPotential_neg_apply_eq_iff]
  rw [besselPotential,Lp.toTemperedDistribution_toLp_eq,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]

end TamingCompatibility.HilbertSobolev

end

end OAI
