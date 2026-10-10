import OAI.NumberTheory.JointDickman.Amplification.CanonicalAffineCost

namespace OAI

/-! # The vanishing budgets used by the actual short-average applications -/
namespace JointDickman
open Filter
open scoped Topology

theorem canonical_affine_application_budget (C d k e : ℝ) :
    Tendsto (fun H => d/H+k*canonicalAffineBase C H+
      (k*canonicalAffineSlope C H+e)/H) atTop (𝓝 0) := by
  have hh := ((canonical_affine_budget C).const_mul k).add
    (tendsto_inv_atTop_zero.const_mul (d+e))
  simp only [mul_zero,add_zero] at hh
  convert hh using 1
  funext H
  ring

end JointDickman

end OAI
