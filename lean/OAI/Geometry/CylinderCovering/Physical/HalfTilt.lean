import OAI.Geometry.CylinderCovering.Physical.CostVariants

namespace OAI

theorem RadialPhysical.half_tilt_linear_bigO : (fun τ : ℝ =>
    RadialPhysical.scaledCost (1/2) (τ/2) (RadialPhysical.linearCap (1/2) (τ/2) (1/120)) -
      RadialPhysical.quadraticCost (1/2) (τ/2) (1/120)) =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun τ => τ^4) := by
  simpa only [one_div, inv_mul_eq_div] using
    RadialPhysical.scaled_linear_bigO (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (0:ℝ)≤1/120) (1/2)

end OAI
