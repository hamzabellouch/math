import OAI.Analysis.CircleDomains.Transfer.ModelScalarPullback
import OAI.Analysis.CircleDomains.Sobolev.ModelLocalEnergy
import OAI.Analysis.CircleDomains.Sobolev.PhysicalRoundIntegrals

namespace OAI

/-! Compact target scalars have finite source L2 norm even when their
values do not descend across the source dust. This permits transport
of the actual vertical error, which need not be constant on holes. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem source_bounded_over_compact_target (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {K : Set EuclideanPlane} (hK : IsCompact K) :
    ∃ R ≥ 0, ∀ z : ℂ, (z : Sphere) ∈ G →
      complexPlaneCoordinates.symm (M.function z) ∈ K → ‖z‖ ≤ R := by
  let C := M.projection '' (planeSphere '' K)
  have hC : IsCompact C := (hK.image continuous_planeSphere).image M.projection_continuous
  have hno : OnePoint.infty ∉ C := by
    rintro ⟨p, ⟨x, hx, rfl⟩, hp⟩
    have hh : planeSphere x = OnePoint.infty :=
      (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hinf).mp
        (by simpa only [extendAtInfinity_infty] using hp)
    exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) hh
  obtain ⟨R, hR⟩ := (hC.image_of_continuousOn
    (continuousOn_finiteCoord_of_avoids_infty hno)).isBounded.exists_norm_le
  refine ⟨max R 0, le_max_right _ _, fun z hz hk => ?_⟩
  apply (hR z ?_).trans (le_max_left _ _)
  refine ⟨(z : Sphere), ?_, by simp only [finiteCoord_coe]⟩
  refine ⟨(M.function z : Sphere), ?_, ?_⟩
  · exact ⟨_, hk, by simp only [planeSphere, complexPlaneCoordinates.apply_symm_apply]⟩
  · simpa only [extendAtInfinity_coe] using M.projection_inverse _ hz

 theorem compact_target_pullback_memLp (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {v : EuclideanPlane → ℝ} (hv : Continuous v) (hs : HasCompactSupport v) :
    MemLp (planeInverseTransport (extendAtInfinity M.function) v) 2
      (volume.restrict (physicalPlaneDomain G)) := by
  let w := planeInverseTransport (extendAtInfinity M.function) v
  have hw (x : EuclideanPlane) : w x = v (complexPlaneCoordinates.symm
      (M.function (complexPlaneCoordinates x))) := by
    change planeInverseTransport (extendAtInfinity M.function) v x = _
    rw [planeInverseTransport_extendAtInfinity]
    simp only [planeSphere, extendAtInfinity_coe, sphereFromPlaneFunction_coe]
  have hD : IsOpen {z : ℂ | (z : Sphere) ∈ G} := hG.preimage OnePoint.continuous_coe
  have hf : ContinuousOn M.function {z : ℂ | (z : Sphere) ∈ G} :=
    (show DifferentiableOn ℂ M.function _ from fun z hz =>
      (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt).continuousOn
  have hc : ContinuousOn w (physicalPlaneDomain G) := by
    have hh := (hv.comp complexPlaneCoordinates.symm.continuous).continuousOn.comp
      (hf.comp complexPlaneCoordinates.continuous.continuousOn (fun _ hx => hx)) (mapsTo_univ _ _)
    exact hh.congr (fun x _ => hw x)
  obtain ⟨R, _, hR⟩ := M.source_bounded_over_compact_target hinf hs.isCompact
  obtain ⟨B, hB⟩ := hv.bounded_above_of_compact_support hs
  have hI : MemLp ((closedBall (0 : EuclideanPlane) R).indicator (fun _ => B)) 2 volume :=
    memLp_indicator_const 2 measurableSet_closedBall B
      (Or.inr (measure_closedBall_lt_top.ne))
  apply (hI.restrict _).of_le (hc.aestronglyMeasurable (isOpen_physicalPlaneDomain hG).measurableSet)
  filter_upwards [ae_restrict_mem (isOpen_physicalPlaneDomain hG).measurableSet] with x hx
  by_cases hxs : complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x)) ∈ tsupport v
  · have hxR : x ∈ closedBall (0 : EuclideanPlane) R := by
      rw [mem_closedBall_zero_iff]
      simpa only [complexPlaneCoordinates_norm] using hR _ hx hxs
    rw [indicator_of_mem hxR, hw]
    exact (hB _).trans (le_abs_self B)
  · rw [hw, image_eq_zero_of_notMem_tsupport hxs, norm_zero]
    exact norm_nonneg _

 theorem compact_target_pullback_energy (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {v : EuclideanPlane → ℝ} (hv : Continuous v) (hs : HasCompactSupport v)
    (V : DeGiorgi.MemW1pWitness 2 v univ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
        (planeInverseTransport (extendAtInfinity M.function) v) (physicalPlaneDomain G),
      (∫ x in physicalPlaneDomain G, W.weakGrad x 0^2+W.weakGrad x 1^2) ≤
        ∫ x in physicalPlaneDomain (extendAtInfinity M.function '' G),
          V.weakGrad x 0^2+V.weakGrad x 1^2 := by
  obtain ⟨hfc, hmap, fi, hfic, hfimap, hl, hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.image_open hp, hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp, hmap, hr, hl⟩
  have hfi : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  exact sobolev_conformal_transport heq M.image_open hG ⟨_, hinf, rfl⟩ hfi hfic hv hs V
    (fun _ _ => rfl) (M.compact_target_pullback_memLp hG hinf hv hs)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
