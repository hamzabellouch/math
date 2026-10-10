import OAI.Analysis.CircleDomains.Sobolev.SphericalAreaLocalization
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

namespace OAI

/-! The explicitly defined stereographic spherical area has finite mass.
Only integrability, not the exact value of the total area, is needed here. -/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem integrable_sphericalAreaDensity : Integrable sphericalAreaDensity := by
  have h : Integrable (fun z : ℂ => ((1 : ℝ) + ‖z‖^2) ^ (-(4 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by norm_num)
  apply (h.const_mul 4).congr
  filter_upwards with z
  have he : -(4 : ℝ) / 2 = -(2 : ℝ) := by norm_num
  rw [he, Real.rpow_neg (by positivity), Real.rpow_two]
  rfl

instance finiteSphericalArea : IsFiniteMeasure sphericalArea := by
  let : IsFiniteMeasure (volume.withDensity (fun z => ENNReal.ofReal (sphericalAreaDensity z))) :=
    isFiniteMeasure_withDensity integrable_sphericalAreaDensity.lintegral_lt_top.ne
  unfold sphericalArea
  infer_instance

end CircleDomainRigidity

end

end OAI
