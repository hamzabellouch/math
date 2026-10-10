import OAI.Probability.SLE.Geometry.HalfPlaneCayleyInverse

namespace OAI

/-! The fixed Cayley chart as a homeomorphism of the closed half-plane
onto the closed disk with the point at infinity removed. -/
noncomputable section
open Set Complex

namespace SLEExactGauge

def closedHalfPlaneCayley :
    {z : ℂ // 0 ≤ z.im} ≃ₜ {w : ℂ // ‖w‖ ≤ 1 ∧ w ≠ 1} where
  toFun z := ⟨halfPlaneCayley z,halfPlaneCayley_norm_le z.property,
    halfPlaneCayley_ne_one z.property⟩
  invFun w := ⟨halfPlaneCayleyInv w,halfPlaneCayleyInv_closed w.property.1⟩
  left_inv z := Subtype.ext (halfPlaneCayleyInv_cayley z.property)
  right_inv w := Subtype.ext (halfPlaneCayley_cayleyInv w.property.2)
  continuous_toFun := (halfPlaneCayley_continuousOn.comp_continuous continuous_subtype_val
    (fun z => z.property)).subtype_mk _
  continuous_invFun := (halfPlaneCayleyInv_continuousOn.comp_continuous continuous_subtype_val
    (fun w => w.property.2)).subtype_mk _

end SLEExactGauge

end

end OAI
