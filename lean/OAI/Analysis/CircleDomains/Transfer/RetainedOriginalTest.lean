import OAI.Analysis.CircleDomains.Rigidity.ProjectedZeroTrace
import OAI.Analysis.CircleDomains.Sobolev.RetainedSobolevContinuations
import OAI.Analysis.CircleDomains.Topology.PrescribedPlaneCoordinate

namespace OAI

/-! Add the constructed zero-trace error back to a retained smooth test.
The result is the continuation of the original test on the same model. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem sphereFromPlaneFunction_sub (u v : EuclideanPlane → ℝ) (p : Sphere) :
    sphereFromPlaneFunction (fun x => u x - v x) p =
      sphereFromPlaneFunction u p - sphereFromPlaneFunction v p := by
  classical
  by_cases hp : p = OnePoint.infty <;> simp [sphereFromPlaneFunction, hp]

namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d id} (R : RetainedRealCircleModel d id Q)

 theorem original_test_witness
    (harea : ExteriorCoefficientAreaTheorem) (hsch : PlanarSchoenflies)
    (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    (i : Fin m) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hus : HasCompactSupport u)
    (hv : Continuous v) (hvs : HasCompactSupport v)
    (hQ : (Q i).quotient = sphereFromPlaneFunction v)
    (htrace : EqOn v u (physicalPlaneDomain d.physicalDomain)ᶜ)
    (D : DeGiorgi.MemW1pWitness 2 (fun x => u x - v x) univ) :
    ∃ H : DeGiorgi.MemW1pWitness 2
      (fun x => R.projectedPlaneFunction hG u (planeSphere x)) univ,
      ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ physicalPlaneDomain
        (extendAtInfinity R.limit.function '' d.physicalDomain) → H.weakGrad x j = 0 := by
  have hQc : Continuous (Q i).quotient := by
    rw [hQ]
    exact continuousOn_univ.mp (sphereFromPlaneFunction_continuousOn isOpen_univ
      hv.continuousOn hvs.isCompact (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  have hQzero : ∀ᶠ p in 𝓝 (id (OnePoint.infty : Sphere)), (Q i).quotient p = 0 := by
    rw [hQ]
    exact sphereFromPlaneFunction_zero_near_infty hvs
  obtain ⟨S, hS, _⟩ := R.exists_continuation_witness harea hsch hG continuous_id i hQc hc hQzero
  have hz : ∀ x ∉ physicalPlaneDomain d.physicalDomain, u x - v x = 0 := by
    intro x hx
    rw [htrace hx, sub_self]
  obtain ⟨K, hK, _⟩ := R.projectedPlaneFunction_zero_trace_witness hG hc
    (hu.sub hv) (hus.sub hvs) hz D
  have hsum : (fun x => R.projectedPlaneFunction hG (fun y => u y - v y) (planeSphere x) +
      R.continuedScalar hG i (planeSphere x)) =
      (fun x => R.projectedPlaneFunction hG u (planeSphere x)) := by
    funext x
    simp only [projectedPlaneFunction, continuedScalar, comp_apply, hQ,
      sphereFromPlaneFunction_sub, sub_add_cancel]
  let H := (K.add S).congr_ae (Eventually.of_forall fun x => congrFun hsum x)
  refine ⟨H, ?_⟩
  intro j
  filter_upwards [hS j] with x hx hxV
  have hnot : complexPlaneCoordinates x ∉
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) := by
    rintro ⟨z, hz, he⟩
    apply hxV
    exact ⟨(z : Sphere), hz, congrArg ((↑) : ℂ → Sphere) he⟩
  change K.weakGrad x j + S.weakGrad x j = 0
  rw [hK j x hxV, hx hnot, add_zero]

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
