import Mathlib
import OAI.Probability.SKValue.Variation.ContactIntegral

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue
lemma IsMinimizer.contact_origin_of_positive {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hγ:IsMinimizer W γ) (hX:IsDiffusion W γ X) (hc:0<γ.coeff 0):contactPotential W γ X 0=0 := by
  have hz:=hγ.contactPotential_ae_zero hX (T:=0) (by constructor <;> norm_num)
  have hh:∀ᵐ s ∂(ENNReal.ofReal (γ.coeff 0) • Measure.dirac (0:ℝ)),contactPotential W γ X s=0 := by
    simpa only [OrderParameter.truncatedMass,Ioc_self,Measure.restrict_empty,zero_add] using hz
  have ha:∀ᵐ s ∂Measure.dirac (0:ℝ),contactPotential W γ X s=0 := by
    exact (Measure.ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hc))).mp hh
  simpa only [ae_dirac_eq, Filter.eventually_pure] using ha
end SKValue

end

end OAI
