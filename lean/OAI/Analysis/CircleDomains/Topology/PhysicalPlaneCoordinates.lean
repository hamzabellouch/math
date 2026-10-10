import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import OAI.Analysis.CircleDomains.Sobolev.PotentialRectangleACL

namespace OAI

/-! The finite physical chart in the Euclidean coordinates used for smoothing. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

def complexPlaneCoordinates : EuclideanPlane ≃L[ℝ] ℂ :=
  euclideanPlaneCoordinates.trans Complex.equivRealProdCLM.symm

@[simp] theorem complexPlaneCoordinates_apply (x : EuclideanPlane) :
    complexPlaneCoordinates x = (⟨x 0, x 1⟩ : ℂ) := rfl

def planeSphere (x : EuclideanPlane) : Sphere := (complexPlaneCoordinates x : Sphere)

theorem continuous_planeSphere : Continuous planeSphere :=
  OnePoint.continuous_coe.comp complexPlaneCoordinates.continuous

def physicalPlaneDomain (G : Set Sphere) : Set EuclideanPlane := planeSphere ⁻¹' G

theorem isOpen_physicalPlaneDomain {G : Set Sphere} (hG : IsOpen G) :
    IsOpen (physicalPlaneDomain G) := hG.preimage continuous_planeSphere

theorem exists_planeSphere_eq {p : Sphere} (hp : p ≠ OnePoint.infty) :
    ∃x : EuclideanPlane, planeSphere x = p := by
  cases p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z =>
    refine ⟨complexPlaneCoordinates.symm z, ?_⟩
    exact congrArg ((↑) : ℂ → Sphere) (complexPlaneCoordinates.apply_symm_apply z)

theorem physical_closed_rectangle_of_coordinate_subset
    {G : Set Sphere} {a b c d : ℝ}
    (hsub : euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ physicalPlaneDomain G) :
    ∀z ∈ closedComplexRectangle a b c d, (z : Sphere) ∈ G := by
  rintro z ⟨p, hp, rfl⟩
  have h := hsub (show euclideanPlaneCoordinates.symm p ∈
      euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp)
  change planeSphere (euclideanPlaneCoordinates.symm p) ∈ G at h
  simpa only [planeSphere, complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply] using h

theorem complex_rectangle_diameter_of_coordinate_diameter {a b c d : ℝ}
    (hdiam : ∀x ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
      ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
        dist (⟨x 0, x 1⟩ : ℂ) (⟨y 0, y 1⟩ : ℂ) ≤ 1) :
    ∀x ∈ closedComplexRectangle a b c d,
      ∀y ∈ closedComplexRectangle a b c d, dist x y ≤ 1 := by
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  have hx : euclideanPlaneCoordinates.symm p ∈
      euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) := by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hy : euclideanPlaneCoordinates.symm q ∈
      euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) := by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hq
  have h := hdiam _ hx _ hy
  change dist (complexPlaneCoordinates (euclideanPlaneCoordinates.symm p))
    (complexPlaneCoordinates (euclideanPlaneCoordinates.symm q)) ≤ 1 at h
  simpa only [complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply] using h

end CircleDomainRigidity

end

end OAI
