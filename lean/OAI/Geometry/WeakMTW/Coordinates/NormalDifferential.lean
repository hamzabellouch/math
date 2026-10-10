import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalFlowLength

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

theorem normalAt_hasFDerivAt_zero (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : (0 : E) ∈ (N.normalAt x).source) :
    HasFDerivAt (N.normalAt x) (N.time • ContinuousLinearMap.id ℝ E) 0 := by
  have hd := NormalCoordinates.hasFDerivAt_flow_zero hS hG hpos N.domain_open
    N.flow_smooth N.initial N.ode (N.base_mem hx) N.time_pos.le (N.source_stays (x, 0) hx)
  have he := hd.comp (0 : E) ((hasFDerivAt_const x (0 : E)).prodMk (hasFDerivAt_id (0 : E)))
  convert! he.fst using 1
  · ext v
    exact N.normalAt_apply x v
  · ext v
    simp

def timeEquiv (N : NormalFlow G S x₀) : E ≃L[ℝ] E :=
  { LinearEquiv.smulOfNeZero ℝ E N.time N.time_pos.ne' with
    continuous_toFun := continuous_const_smul N.time
    continuous_invFun := continuous_const_smul N.time⁻¹ }

omit [FiniteDimensional ℝ E] in
@[simp] theorem timeEquiv_coe (N : NormalFlow G S x₀) :
    (N.timeEquiv : E →L[ℝ] E) = N.time • ContinuousLinearMap.id ℝ E := by
  ext v
  rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem timeEquiv_symm_coe (N : NormalFlow G S x₀) :
    (N.timeEquiv.symm : E →L[ℝ] E) = N.time⁻¹ • ContinuousLinearMap.id ℝ E := by
  ext v
  rfl

 theorem normalAt_inverse_hasFDerivAt_center (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hx : (0 : E) ∈ (N.normalAt x).source) :
    HasFDerivAt (N.normalAt x).symm (N.time⁻¹ • ContinuousLinearMap.id ℝ E) x := by
  have he := N.normalAt_zero hS hG hpos hx
  have hmem : x ∈ (N.normalAt x).target := by
    simpa only [he] using (N.normalAt x).map_source hx
  have hi : (N.normalAt x).symm x = 0 := by
    simpa only [he] using (N.normalAt x).left_inv hx
  have hd : HasFDerivAt (N.normalAt x) (N.timeEquiv : E →L[ℝ] E) ((N.normalAt x).symm x) := by
    rw [hi, timeEquiv_coe]
    exact N.normalAt_hasFDerivAt_zero hS hG hpos hx
  simpa only [timeEquiv_symm_coe] using (N.normalAt x).hasFDerivAt_symm hmem hd

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
