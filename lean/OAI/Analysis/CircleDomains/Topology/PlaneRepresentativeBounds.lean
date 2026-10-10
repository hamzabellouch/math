import OAI.Analysis.CircleDomains.Topology.PlaneQuotientRepresentative

namespace OAI

/-! Positivity and unit bounds for the descended physical representative. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem sphereFromPlaneFunction_mem_Icc {G : Set Sphere} {w : EuclideanPlane → ℝ}
    (hw : ∀x ∈ physicalPlaneDomain G, w x ∈ Icc 0 1) :
    ∀p ∈ G, sphereFromPlaneFunction w p ∈ Icc 0 1 := by
  intro p hp
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    rw [sphereFromPlaneFunction_coe]
    apply hw
    change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∈ G
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp

theorem quotientPlaneRepresentative_mem_Icc (d : PathCodeData X Sphere) {w : EuclideanPlane → ℝ}
    (hw : ∀x ∈ physicalPlaneDomain d.physicalDomain, w x ∈ Icc 0 1) :
    ∀x, quotientPlaneRepresentative d w x ∈ Icc 0 1 := by
  classical
  intro x
  by_cases hx : x ∈ d.quotientDomain
  · rw [quotientPlaneRepresentative, dite_eq_left hx]
    exact sphereFromPlaneFunction_mem_Icc hw _ (d.domainEquiv.symm ⟨x, hx⟩).property
  · simp only [quotientPlaneRepresentative, dite_eq_right hx, mem_Icc, le_refl, zero_le_one, and_self]

end CircleDomainRigidity

end

end OAI
