import OAI.Analysis.CircleDomains.Sobolev.PhysicalSamplingPartition

namespace OAI

/-! Descend a physical planar function through the actual domain homeomorphism. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

def sphereFromPlaneFunction (w : EuclideanPlane → ℝ) (p : Sphere) : ℝ := by
  classical
  exact if p = OnePoint.infty then 0 else w (complexPlaneCoordinates.symm (finiteCoord p))

@[simp] theorem sphereFromPlaneFunction_coe (w : EuclideanPlane → ℝ) (z : ℂ) :
    sphereFromPlaneFunction w (z : Sphere) = w (complexPlaneCoordinates.symm z) := by
  simp [sphereFromPlaneFunction, finiteCoord]

def quotientPlaneRepresentative (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ)
    (x : X) : ℝ := by
  classical
  exact if hx : x ∈ d.quotientDomain then
    sphereFromPlaneFunction w (d.domainEquiv.symm ⟨x, hx⟩).val else 0

theorem quotientPlaneRepresentative_on_domain
    (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ)
    (p : Sphere) (hp : p ∈ d.physicalDomain) :
    quotientPlaneRepresentative d w (d.domainEquiv ⟨p, hp⟩).val =
      sphereFromPlaneFunction w p := by
  simp only [quotientPlaneRepresentative, dite_eq_left (d.domainEquiv ⟨p, hp⟩).property]
  have he : (⟨(d.domainEquiv ⟨p, hp⟩).val, (d.domainEquiv ⟨p, hp⟩).property⟩ :
      d.quotientDomain) = d.domainEquiv ⟨p, hp⟩ := rfl
  rw [he, Homeomorph.symm_apply_apply]

theorem quotientPlaneRepresentative_plane
    (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ) (π : Sphere → X)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain d.physicalDomain) :
    quotientPlaneRepresentative d w (π (planeSphere x)) = w x := by
  have hp : planeSphere x ∈ d.physicalDomain := hx
  rw [← he ⟨planeSphere x, hp⟩, quotientPlaneRepresentative_on_domain d w _ hp]
  change sphereFromPlaneFunction w (complexPlaneCoordinates x : Sphere) = w x
  rw [sphereFromPlaneFunction_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem quotient_finite_plane_covers
    (d : PathCodeData X Sphere) (π : Sphere → X)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val) :
    d.quotientDomain \ {π OnePoint.infty} ⊆ (π ∘ planeSphere) '' physicalPlaneDomain d.physicalDomain := by
  intro y hy
  let p : d.physicalDomain := d.domainEquiv.symm ⟨y, hy.1⟩
  have hπp : π p.val = y := by
    rw [← he p]
    exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨y, hy.1⟩)
  have hp : p.val ≠ OnePoint.infty := by
    intro hinf
    exact hy.2 (by simpa only [mem_singleton_iff, hinf] using hπp.symm)
  obtain ⟨x, hx⟩ := exists_planeSphere_eq hp
  refine ⟨x, ?_, ?_⟩
  · change planeSphere x ∈ d.physicalDomain
    rw [hx]
    exact p.property
  · change π (planeSphere x) = y
    rwa [hx]

end CircleDomainRigidity

end

end OAI
