import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.MinimizerCompactness
import OAI.Geometry.WeakMTW.Variations.ActionBranch

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem branch_zero_hessian {x z : M} (B : ActionBranch (n := n) x z)
    (hB : stateChart x (⟨x,0⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    (ξ : TangentSpace (model n) x) :
    branchHessianDiag x z B.coord 0 ξ = inner ℝ ξ ξ := by
  have hw : Tendsto (fun r : ℝ => r•ξ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_smul] using ((show Continuous (fun r : ℝ => r•ξ) from continuous_id.smul continuous_const).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hI : ∀ᶠ r : ℝ in 𝓝[>] 0, r•ξ ∈ injectivityDomain x :=
    hw ((injectivityDomain_open x).mem_nhds (zero_mem_injectivity x))
  have hlim := B.hessian_limit hB ξ hw hI
  have hconst : ∀ᶠ r : ℝ in 𝓝[>] 0, actionHessian x (r•ξ) ξ ξ = inner ℝ ξ ξ := by
    filter_upwards [hI,self_mem_nhdsWithin] with r hr hrpos
    have hh := actionHessian_radial x hr ξ
    rw [map_smul,inner_smul_right] at hh
    simp only [smul_eq_mul] at hh
    exact mul_left_cancel₀ (ne_of_gt hrpos) hh
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hconst))

 theorem branch_zero_raw_hessian {x z : M} (B : ActionBranch (n := n) x z)
    (hB : stateChart x (⟨x,0⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    (ξ : TangentSpace (model n) x) :
    fderiv ℝ (fderiv ℝ B.value) (chartAt (Model n) x x,chartAt (Model n) z x)
      (tangentChartLinear x ξ,0) (tangentChartLinear x ξ,0) = inner ℝ ξ ξ := by
  have hh := branch_zero_hessian B hB ξ
  simpa only [branchHessianDiag,exp_zero,map_zero,add_zero,ActionBranch.value] using hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
