import OAI.Analysis.CircleDomains.Topology.CompactScalarContinuation
import OAI.Analysis.CircleDomains.Topology.SpherePlaneContinuity
import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneEnergyTransport

namespace OAI

/-! Continue any compact planar test through the actual matched-end
projection. This construction does not require the test to be smooth. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem sphereFromPlaneFunction_zero_near_infty
    {u : EuclideanPlane → ℝ} (hs : HasCompactSupport u) :
    ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), sphereFromPlaneFunction u p = 0 := by
  let K := complexPlaneCoordinates '' tsupport u
  have hK : IsCompact K := hs.isCompact.image complexPlaneCoordinates.continuous
  have hN : (((↑) : ℂ → Sphere) '' K)ᶜ ∈ 𝓝 (OnePoint.infty : Sphere) :=
    (OnePoint.isOpen_compl_image_coe.mpr ⟨hK.isClosed, hK⟩).mem_nhds
      OnePoint.infty_notMem_image_coe
  filter_upwards [hN] with p hp
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    rw [sphereFromPlaneFunction_coe]
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hp ⟨z, ⟨complexPlaneCoordinates.symm z, hz,
      complexPlaneCoordinates.apply_symm_apply z⟩, rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d id} (R : RetainedRealCircleModel d id Q)

 def projectedPlaneFunction (hG : IsOpen d.physicalDomain) (u : EuclideanPlane → ℝ) :
    Sphere → ℝ := sphereFromPlaneFunction u ∘ R.limit.sourceProjection hG id

 theorem projectedPlaneFunction_continuous (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u) :
    Continuous (R.projectedPlaneFunction hG u) := by
  have huc : Continuous (sphereFromPlaneFunction u) := continuousOn_univ.mp
    (sphereFromPlaneFunction_continuousOn isOpen_univ hu.continuousOn hs.isCompact
      (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  exact huc.comp (R.limit.sourceProjection_continuous hG id continuous_id hc)

 theorem projectedPlaneFunction_hasCompactSupport (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {u : EuclideanPlane → ℝ} (hs : HasCompactSupport u) :
    HasCompactSupport (fun x => R.projectedPlaneFunction hG u (planeSphere x)) := by
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  have hS := (R.limit.sourceProjection_continuous hG id continuous_id hc).tendsto OnePoint.infty
  have hSinf : R.limit.sourceProjection hG id OnePoint.infty = OnePoint.infty :=
    R.limit.sourceProjection_on_image hG id hinf
  rw [hSinf] at hS
  have hzero := hS.eventually (sphereFromPlaneFunction_zero_near_infty hs)
  have ht : Tendsto ((↑) : ℂ → Sphere) (coclosedCompact ℂ) (𝓝 OnePoint.infty) :=
    OnePoint.tendsto_coe_infty
  have hh : HasCompactSupport (fun z : ℂ => R.projectedPlaneFunction hG u z) := by
    rw [hasCompactSupport_iff_eventuallyEq]
    exact ht.eventually hzero
  exact hh.comp_homeomorph complexPlaneCoordinates.toHomeomorph

 theorem projectedPlaneFunction_zero_off_image (hG : IsOpen d.physicalDomain)
    {u : EuclideanPlane → ℝ} (hz : ∀ x ∉ physicalPlaneDomain d.physicalDomain, u x = 0)
    {p : Sphere} (hp : p ∉ extendAtInfinity R.limit.function '' d.physicalDomain) :
    R.projectedPlaneFunction hG u p = 0 := by
  rw [projectedPlaneFunction, comp_apply, R.limit.sourceProjection_off_image hG id hp]
  let A := R.limit.chosenSourceEnd hG p hp
  change sphereFromPlaneFunction u A.source = 0
  have hA : A.source ∉ d.physicalDomain := A.outside
  cases hq : A.source using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    rw [sphereFromPlaneFunction_coe]
    apply hz
    change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∉ d.physicalDomain
    simpa only [ContinuousLinearEquiv.apply_symm_apply, hq] using hA

 theorem projectedPlaneFunction_on_image (hG : IsOpen d.physicalDomain)
    (u : EuclideanPlane → ℝ) {p : Sphere} (hp : p ∈ d.physicalDomain) :
    R.projectedPlaneFunction hG u (extendAtInfinity R.limit.function p) =
      sphereFromPlaneFunction u p := by
  rw [projectedPlaneFunction, comp_apply, R.limit.sourceProjection_on_image hG id hp]
  rfl

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
