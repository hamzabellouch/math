import OAI.Analysis.CircleDomains.Topology.SpherePlaneContinuity
import OAI.Analysis.CircleDomains.Uniformization.PrincipalCoefficientLimit
import OAI.Analysis.CircleDomains.Sobolev.QuasiconformalSobolev

namespace OAI

/-! Scalar models with a globally deformed round complement. This is the
smaller class needed for coefficient extremality: it contains the actual
circle models and is closed under plane homeomorphisms. The deformation
retains every complementary component, rather than just its boundary. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 structure CompactScalarModel (G : Set Sphere) {m : ℕ}
    (u : Fin m → EuclideanPlane → ℝ) where
  function : ℂ → ℂ
  coefficient : ℂ
  coefficient_limit : HasPrincipalCoefficient function coefficient
  conformal : IsConformalEquivalence (extendAtInfinity function) G (extendAtInfinity function '' G)
  roundDomain : Set Sphere
  round_circle : IsCircleDomain roundDomain
  deformation : ℂ ≃ₜ ℂ
  image_eq : extendAtInfinity function '' G = deformation.onePointCongr '' roundDomain
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
  scalar_compact : ∀ i, HasCompactSupport
    (fun x => sphereFromPlaneFunction (u i) (projection (planeSphere x)))

 namespace CompactScalarModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem normalized (M : CompactScalarModel G u) :
    IsPrincipalNormalized (extendAtInfinity M.function) :=
  isPrincipalNormalized_extendAtInfinity M.coefficient_limit.bigO

 theorem image_open (M : CompactScalarModel G u) :
    IsOpen (extendAtInfinity M.function '' G) := by
  rw [M.image_eq]
  exact M.deformation.onePointCongr.isOpenMap _ M.round_circle.1

 theorem image_connected (M : CompactScalarModel G u) :
    IsConnected (extendAtInfinity M.function '' G) := by
  rw [M.image_eq]
  exact M.round_circle.2.1.image _ M.deformation.onePointCongr.continuous.continuousOn

 theorem scalar_continuous (M : CompactScalarModel G u)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i)) (i : Fin m) :
    Continuous (fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))) := by
  have huc : Continuous (sphereFromPlaneFunction (u i)) := continuousOn_univ.mp
    (sphereFromPlaneFunction_continuousOn isOpen_univ (hu i).continuousOn (hs i).isCompact
      (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  exact huc.comp (M.projection_continuous.comp continuous_planeSphere)

 end CompactScalarModel

end CircleDomainRigidity

end

end OAI
