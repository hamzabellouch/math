import OAI.Analysis.CircleDomains.Topology.PlaneQuotientRepresentative

namespace OAI

/-! A compactly supported planar smoothing descends continuously across infinity. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem sphereFromPlaneFunction_continuousAt_coe
    {w : EuclideanPlane → ℝ} {z : ℂ}
    (hw : ContinuousAt w (complexPlaneCoordinates.symm z)) :
    ContinuousAt (sphereFromPlaneFunction w) (z : Sphere) := by
  apply OnePoint.continuousAt_coe.mpr
  have he : sphereFromPlaneFunction w ∘ ((↑) : ℂ → Sphere) =
      w ∘ complexPlaneCoordinates.symm := by
    funext z
    exact sphereFromPlaneFunction_coe w z
  rw [he]
  exact hw.comp complexPlaneCoordinates.symm.continuous.continuousAt

theorem sphereFromPlaneFunction_continuousAt_infty
    {w : EuclideanPlane → ℝ} {K : Set EuclideanPlane} (hK : IsCompact K)
    (hw : ∀x ∉ K, w x = 0) :
    ContinuousAt (sphereFromPlaneFunction w) OnePoint.infty := by
  apply OnePoint.continuousAt_infty.mpr
  intro S hS
  have hK' : IsCompact (complexPlaneCoordinates '' K) := hK.image complexPlaneCoordinates.continuous
  refine ⟨complexPlaneCoordinates '' K, hK'.isClosed, hK', ?_⟩
  intro z hz
  change sphereFromPlaneFunction w (z : Sphere) ∈ S
  rw [sphereFromPlaneFunction_coe, hw _ ?_]
  · apply mem_of_mem_nhds
    simpa [sphereFromPlaneFunction] using hS
  · intro hx
    exact hz ⟨complexPlaneCoordinates.symm z, hx, complexPlaneCoordinates.apply_symm_apply z⟩

theorem sphereFromPlaneFunction_continuousOn
    {G : Set Sphere} (hG : IsOpen G) {w : EuclideanPlane → ℝ}
    (hw : ContinuousOn w (physicalPlaneDomain G))
    {K : Set EuclideanPlane} (hK : IsCompact K) (hzero : ∀x ∉ K, w x = 0) :
    ContinuousOn (sphereFromPlaneFunction w) G := by
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact (sphereFromPlaneFunction_continuousAt_infty hK hzero).continuousWithinAt
  | coe z =>
    have hx : complexPlaneCoordinates.symm z ∈ physicalPlaneDomain G := by
      change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∈ G
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp
    exact (sphereFromPlaneFunction_continuousAt_coe
      (hw.continuousAt ((isOpen_physicalPlaneDomain hG).mem_nhds hx))).continuousWithinAt

theorem quotientPlaneRepresentative_continuousOn
    (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ)
    (hw : ContinuousOn (sphereFromPlaneFunction w) d.physicalDomain) :
    ContinuousOn (quotientPlaneRepresentative d w) d.quotientDomain := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hh : Continuous (fun x : d.quotientDomain =>
      sphereFromPlaneFunction w (d.domainEquiv.symm x).val) :=
    hw.domRestrict.comp d.domainEquiv.symm.continuous
  convert hh using 1
  funext x
  change quotientPlaneRepresentative d w x.val = _
  exact dite_eq_left x.property

end CircleDomainRigidity

end

end OAI
