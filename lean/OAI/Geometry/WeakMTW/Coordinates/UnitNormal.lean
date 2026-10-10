import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalEndpoint

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem locally_exists_unit_ray (x : M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : M, dist x y < ε → 0 < dist x y →
      ∃ p : TangentBundle (model n) M, p.1 = x ∧ ‖p.2‖ = 1 ∧ geodesic p (dist x y) = y := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (locally_exists_minimizing_vector (n := n) x)
  refine ⟨ε,hε,?_⟩
  intro y hy hpos
  obtain ⟨v,he,hv⟩ := hball (by simpa only [Metric.mem_ball,dist_comm] using hy)
  let p : TangentBundle (model n) M := ⟨x,(dist x y)⁻¹ • v⟩
  refine ⟨p,rfl,?_,?_⟩
  · change ‖(dist x y)⁻¹ • v‖ = 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos),hv,inv_mul_cancel₀ hpos.ne']
  · rw [← exp_mul_eq_geodesic]
    change exp x (dist x y • ((dist x y)⁻¹ • v)) = y
    rwa [smul_smul,mul_inv_cancel₀ hpos.ne',one_smul]
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
