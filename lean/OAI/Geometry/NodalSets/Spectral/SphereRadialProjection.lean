import OAI.Geometry.NodalSets.Charts.SphereCovectorRestriction

namespace OAI

namespace Yau.Target
open Manifold
open scoped RealInnerProductSpace
noncomputable section

def sphereTangentProjection (x : Base) (v : AmbientBase) : AmbientBase :=
  v - ⟪(x : AmbientBase),v⟫ • (x : AmbientBase)

lemma sphere_radial_norm (x : Base) : ‖(x : AmbientBase)‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using x.property

lemma sphereTangentProjection_orthogonal (x : Base) (v : AmbientBase) :
    ⟪(x : AmbientBase),sphereTangentProjection x v⟫ = 0 := by
  simp [sphereTangentProjection, inner_sub_right, real_inner_smul_right]

lemma sphereTangentProjection_norm (x : Base) (v : AmbientBase) :
    ‖sphereTangentProjection x v‖^2 + ⟪(x : AmbientBase),v⟫^2 = ‖v‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sphereTangentProjection, inner_sub_left, inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, sq_abs, sphere_radial_norm,mul_one,real_inner_comm v (x : AmbientBase)]
  ring

lemma sphereTangentProjection_restriction (x : Base) (v : AmbientBase) :
    sphereCovectorRestriction x (sphereTangentProjection x v) = sphereCovectorRestriction x v := by
  simp only [sphereTangentProjection,map_sub,map_smul,sphereCovectorRestriction_radial,
    smul_zero,sub_zero]

end
end Yau.Target

end OAI
