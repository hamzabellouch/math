import OAI.Analysis.CircleDomains.Topology.PlaneQuotientRepresentative

namespace OAI

/-! The finite physical chart covers the quotient away from the image of infinity. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem quotient_injOn_physical_domain
    (d : PathCodeData X Sphere) (π : Sphere → X)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val) :
    InjOn π d.physicalDomain := by
  intro x hx y hy hxy
  have h : d.domainEquiv ⟨x, hx⟩ = d.domainEquiv ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa only [he] using hxy
  exact congrArg Subtype.val (d.domainEquiv.injective h)

theorem quotient_finite_plane_mapsTo
    (d : PathCodeData X Sphere) (π : Sphere → X)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hinf : OnePoint.infty ∈ d.physicalDomain) :
    MapsTo (π ∘ planeSphere) (physicalPlaneDomain d.physicalDomain)
      (d.quotientDomain \ {π OnePoint.infty}) := by
  intro x hx
  have hp : planeSphere x ∈ d.physicalDomain := hx
  constructor
  · change π (planeSphere x) ∈ d.quotientDomain
    rw [← he ⟨planeSphere x, hp⟩]
    exact (d.domainEquiv ⟨planeSphere x, hp⟩).property
  · intro hh
    have heq := quotient_injOn_physical_domain d π he hp hinf hh
    exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) heq

end CircleDomainRigidity

end

end OAI
