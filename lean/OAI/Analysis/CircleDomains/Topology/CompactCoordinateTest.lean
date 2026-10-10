import OAI.Analysis.CircleDomains.Selection.SignedTestFamily
import OAI.Analysis.CircleDomains.Sobolev.CompactMollifierSampling

namespace OAI

/-! An axial coordinate on a bounded sphere complement can be represented
by a smooth compact planar test. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem exists_smooth_compact_coordinate_test {H : Set Sphere}
    (hH : IsOpen H) (hinf : OnePoint.infty ∈ H) (i : Fin 2) :
    ∃ Φ : EuclideanPlane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      ∀ z : ℂ, (z : Sphere) ∈ Hᶜ →
        sphereFromPlaneFunction Φ (z : Sphere) = (complexPlaneCoordinates.symm z) i := by
  have hK : IsCompact (physicalPlaneDomain H)ᶜ := by
    have hh := (isCompact_finite_preimage hH.isClosed_compl (not_not.mpr hinf)).image
      complexPlaneCoordinates.symm.continuous
    convert hh using 1
    ext x
    simp only [mem_compl_iff,physicalPlaneDomain,mem_preimage,mem_image]
    constructor
    · intro hx
      exact ⟨complexPlaneCoordinates x,hx,complexPlaneCoordinates.symm_apply_apply x⟩
    · rintro ⟨z,hz,rfl⟩
      simpa only [planeSphere,ContinuousLinearEquiv.apply_symm_apply] using hz
  obtain ⟨η,V,hη,hsη,_,_,_,hKV,hηV⟩ :=
    exists_smooth_compact_cutoff_one_near hK isOpen_univ (subset_univ _)
  refine ⟨(fun x => η x*x i),hη.mul (by fun_prop),hsη.mul_right,?_⟩
  intro z hz
  rw [sphereFromPlaneFunction_coe]
  have hx : complexPlaneCoordinates.symm z ∈ (physicalPlaneDomain H)ᶜ := by
    simpa only [mem_compl_iff,physicalPlaneDomain,mem_preimage,planeSphere,
      ContinuousLinearEquiv.apply_symm_apply] using hz
  rw [hηV _ (hKV hx),one_mul]

end CircleDomainRigidity

end

end OAI
