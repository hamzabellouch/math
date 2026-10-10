import OAI.Analysis.CircleDomains.Topology.SpherePlaneContinuity
import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneSobolev
import OAI.Analysis.CircleDomains.Topology.LimitSphereExtension

namespace OAI

/-! The actual retained circle-model data, separated from their construction. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

structure CompactScalarCircleModel (G : Set Sphere) {m : ℕ}
    (u : Fin m → EuclideanPlane → ℝ) where
  function : ℂ → ℂ
  normalized : IsPrincipalNormalized (extendAtInfinity function)
  conformal : IsConformalEquivalence (extendAtInfinity function) G (extendAtInfinity function '' G)
  circle : IsCircleDomain (extendAtInfinity function '' G)
  projection : Sphere → Sphere
  projection_continuous : Continuous projection
  projection_inverse : ∀ p ∈ G, projection (extendAtInfinity function p) = p
  projection_outside : ∀ p ∉ extendAtInfinity function '' G, projection p ∈ Gᶜ
  projection_component : ∀ p ∉ extendAtInfinity function '' G,
    ∀ q ∈ connectedComponentIn (extendAtInfinity function '' G)ᶜ p, projection q = projection p
  witness : ∀ i, DeGiorgi.MemW1pWitness 2
    (fun x => sphereFromPlaneFunction (u i) (projection (planeSphere x))) univ
  gradient_zero : ∀ i j, ∀ᵐ x ∂volume,
    x ∉ physicalPlaneDomain (extendAtInfinity function '' G) → (witness i).weakGrad x j = 0

end CircleDomainRigidity

end

end OAI
