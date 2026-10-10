import OAI.Geometry.CylinderCovering.Nilpotent.Profile

namespace OAI

theorem CylinderCovering.Nilpotent.Profile.zero_field_fderiv_square_zero (p t : ℝ) (ht : t ≠ 0) :
    (fderiv ℝ (CylinderCovering.Nilpotent.Profile.field (fun _ => 0) (fun _ => 0))
      (RuledApproximation.vec2 (p * t) t)).comp
    (fderiv ℝ (CylinderCovering.Nilpotent.Profile.field (fun _ => 0) (fun _ => 0))
      (RuledApproximation.vec2 (p * t) t)) = 0 := by
  exact CylinderCovering.Nilpotent.Profile.field_fderiv_square_zero
    (hasDerivAt_const p 0) (hasDerivAt_const p 0) ht (by simp)

end OAI
