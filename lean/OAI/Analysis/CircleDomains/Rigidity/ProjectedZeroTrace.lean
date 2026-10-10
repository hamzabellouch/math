import OAI.Analysis.CircleDomains.Topology.ProjectedPlaneFunction
import OAI.Analysis.CircleDomains.Rigidity.ZeroTraceConformalTransport

namespace OAI

/-! The zero-trace error for a retained circle model has an actual global
Sobolev continuation with zero complementary gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d id} (R : RetainedRealCircleModel d id Q)

 theorem projectedPlaneFunction_zero_trace_witness
    (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ physicalPlaneDomain d.physicalDomain, u x = 0)
    (H : DeGiorgi.MemW1pWitness 2 u univ) :
    ∃ K : DeGiorgi.MemW1pWitness 2
      (fun x => R.projectedPlaneFunction hG u (planeSphere x)) univ,
      (∀ i : Fin 2, ∀ x ∉ physicalPlaneDomain
        (extendAtInfinity R.limit.function '' d.physicalDomain), K.weakGrad x i = 0) ∧
      (∫ x, K.weakGrad x 0 ^ 2 + K.weakGrad x 1 ^ 2) ≤
        ∫ x in physicalPlaneDomain d.physicalDomain, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2 := by
  let f := extendAtInfinity R.limit.function
  let V := f '' d.physicalDomain
  have hV : IsOpen V := R.limit.conformal.1.isOpen_image hG hG (Subset.refl _)
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  obtain ⟨fi, heq⟩ := R.limit.conformal.exists_smooth_inverse hG hV
  change IsSmoothSphereEquivalence f fi d.physicalDomain V at heq
  have hv : EqOn (fun x => R.projectedPlaneFunction hG u (planeSphere x))
      (planeInverseTransport fi u) (physicalPlaneDomain V) := by
    intro x hx
    have hr := R.projectedPlaneFunction_on_image hG u (heq.mapsTo_inv hx)
    change R.projectedPlaneFunction hG u (f (fi (planeSphere x))) = _ at hr
    rw [heq.right_inv _ hx] at hr
    refine hr.trans ?_
    change sphereFromPlaneFunction u (fi (planeSphere x)) =
      u (complexPlaneCoordinates.symm (finiteCoord (fi (planeSphere x))))
    have hfinite : fi (planeSphere x) ≠ OnePoint.infty := heq.finite_inv hinf rfl hx
    rw [sphereFromPlaneFunction, ite_eq_right hfinite]
  exact zero_trace_conformal_transport heq hG hV hinf rfl R.limit.conformal.1 hu hs H hv
    ((R.projectedPlaneFunction_continuous hG hc hu hs).comp continuous_planeSphere)
    (R.projectedPlaneFunction_hasCompactSupport hG hc hs)
    (fun x hx => R.projectedPlaneFunction_zero_off_image hG hz hx)

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
