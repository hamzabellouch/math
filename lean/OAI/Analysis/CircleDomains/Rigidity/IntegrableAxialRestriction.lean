import OAI.Analysis.CircleDomains.Rigidity.AxialLineIntegral
import OAI.Analysis.CircleDomains.Rigidity.AxialLineDifferentiation

namespace OAI

/-! Fubini for restrictions to actual measurable plane sets. -/
open Set Function Filter MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem integrable_axial_restriction_ae {U : Set ℂ} (hU : MeasurableSet U)
    {q : ℂ → ℝ} (hq : IntegrableOn q U volume) (i : Fin 2) :
    ∀ᵐ y ∂volume, IntegrableOn (fun x => q (complexCoordinateLine i y x))
      {x | complexCoordinateLine i y x ∈ U} volume := by
  have hi : Integrable (U.indicator q) volume := (integrable_indicator_iff hU).mpr hq
  filter_upwards [(integral_axial_slices hi i).1] with y hy
  apply (integrable_indicator_iff
    (hU.preimage (complexCoordinateLine_contDiff i y).continuous.measurable)).mp
  convert hy using 1
  funext x
  by_cases h : complexCoordinateLine i y x ∈ U <;> simp [h]

end CircleDomainRigidity

end

end OAI
