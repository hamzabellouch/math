import OAI.Probability.GammaPassage.ASMeanBridge
import OAI.Probability.GammaPassage.RealDirectionBridge
import OAI.Probability.GammaPassage.SequenceSummability

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem GammaEnvironment.isTimeConstant
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    IsTimeConstant P τ (gammaMeanNorm h hs hr) := by
  apply h.isTimeConstant_of_ae_lattice_limits hs hr
  intro z
  exact h.ae_lattice_limit_of_summable_deviations hs hr z
    (fun k => h.normalized_ray_deviations_tsum_ne_top hs hr z k)

end GammaFPP

end OAI
