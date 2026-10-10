import OAI.Geometry.Relativity.CKS.SchwarzschildCoordinates
import OAI.Geometry.Relativity.CKS.BoundarySmooth
import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma boundary_height (p : Boundary Exterior) : height p.val = 0 :=
  (boundary_iff p.val).mp p.property

def boundarySphere : Boundary Exterior ≃ₜ Sphere where
  toFun p := p.val.2
  invFun n := ⟨(⟨0,le_rfl⟩,n),(boundary_iff _).mpr rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact (boundary_height p).symm
    · rfl
  right_inv n := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

lemma boundarySphere_smooth : ContMDiff I2 I2 ∞ boundarySphere :=
  angular_smooth.comp CKSBoundarySurface.inclusion_smooth
lemma mfderiv_boundarySphere (p : Boundary Exterior) :
    mfderiv I2 I2 boundarySphere p = ContinuousLinearMap.id ℝ E2 := by
  have h := mfderiv_comp p (angular_smooth.mdifferentiable (by simp) p.val)
    (CKSBoundarySurface.inclusion_smooth.mdifferentiable (by simp) p)
  change mfderiv I2 I2 boundarySphere p = _ at h
  rw [mfderiv_angular,(CKSBoundarySurface.inclusion_hasMFDeriv p).mfderiv] at h
  rw [h]
  apply ContinuousLinearMap.ext
  intro v
  exact drop_lift v

lemma boundarySphere_symm_chart (p : Sphere) :
    writtenInExtChartAt I2 I2 p boundarySphere.symm =ᶠ[𝓝 (extChartAt I2 p p)] id := by
  filter_upwards [extChartAt_target_mem_nhds p] with z hz
  change dropPlane (I3 (chartAt H3 (boundarySphere.symm p).val
    (boundarySphere.symm ((extChartAt I2 p).symm z)).val)) = z
  change dropPlane (join (0, chartAt E2 p ((extChartAt I2 p).symm z))) = z
  rw [drop_join]
  exact (extChartAt I2 p).right_inv hz

lemma boundarySphere_symm_smooth : ContMDiff I2 I2 ∞ boundarySphere.symm := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨boundarySphere.symm.continuous.continuousAt,?_⟩
  apply contDiffAt_id.contDiffWithinAt.congr_of_eventuallyEq
    ((boundarySphere_symm_chart p).filter_mono nhdsWithin_le_nhds)
  exact (boundarySphere_symm_chart p).self_of_nhds

lemma mfderiv_boundarySphere_symm (p : Sphere) :
    mfderiv I2 I2 boundarySphere.symm p = ContinuousLinearMap.id ℝ E2 := by
  have h : HasMFDerivAt I2 I2 boundarySphere.symm p (ContinuousLinearMap.id ℝ E2) := by
    refine ⟨boundarySphere.symm.continuous.continuousAt,?_⟩
    exact (hasFDerivAt_id _).hasFDerivWithinAt.congr_of_eventuallyEq
      ((boundarySphere_symm_chart p).filter_mono nhdsWithin_le_nhds)
      ((boundarySphere_symm_chart p).self_of_nhds)
  exact h.mfderiv

lemma boundary_compact : IsCompact (I3.boundary Exterior) := by
  have : CompactSpace (Boundary Exterior) := boundarySphere.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

end CKSSchwarzschild

end

end OAI
