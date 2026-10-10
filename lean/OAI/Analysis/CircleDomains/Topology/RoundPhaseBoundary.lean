import OAI.Analysis.CircleDomains.Reflection.RegularPhaseSides
import OAI.Analysis.CircleDomains.Topology.AnalyticCircleImage

namespace OAI

/-! The selected limiting disk is actually omitted, and its entire
circle is a boundary of the image of the original domain. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}
variable {P:PhaseCollar C i} (L:RegularPhaseLimit P)

lemma RegularPhaseLimit.circle_image :
    L.boundaryMap '' sphere (0:ℂ) 1=sphere L.center L.radius :=
  analytic_circle_image_eq (isOpen_symmetricCircleAnnulus P.radius)
    (unit_circle_subset_symmetricCircleAnnulus P.radius_gt)
    L.holomorphic L.injective L.radius_pos.le (fun _ hz => L.boundary_iff hz)

lemma RegularPhaseLimit.finite_map_properties :
    DifferentiableOn ℂ L.map C.planeRegion ∧ IsOpen (L.map '' C.planeRegion) ∧
      InjOn L.map C.planeRegion := by
  obtain ⟨hd,ho,hi⟩ := L.conformal.1.finite_open_embedding C.region_open
    L.conformal.bijOn.injOn C.infty_mem_region L.normalized.1
  simp only [extendAtInfinity_coe,finiteCoord_coe] at hd ho hi
  exact ⟨hd,ho C.planeRegion C.planeRegion_open (Subset.refl _),hi⟩

lemma RegularPhaseLimit.omitted_disk : closedBall L.center L.radius⊆(L.map '' C.planeRegion)ᶜ := by
  apply omitted_closedBall_limit hurwitzZeroFreeLimit C.planeRegion_open C.planeRegion_connected
    (Eventually.of_forall (fun n => ?_))
    (fun n => (selectedRadius_pos C (cyclicSchedule m) (visitTime (L.subsequence n) i)).le)
    L.radius_pos.le L.map_tendsto L.centers_tendsto L.radii_tendsto
    (C.not_constant_of_injOn L.finite_map_properties.2.2)
  exact ⟨((cumulativeMap_conformal C (cyclicSchedule m)
    (visitTime (L.subsequence n) i+1)).1.finite_open_embedding C.region_open
    (cumulativeMap_conformal C (cyclicSchedule m) (visitTime (L.subsequence n) i+1)).bijOn.injOn
    C.infty_mem_region (cumulativeMap_principal C (cyclicSchedule m)
      (visitTime (L.subsequence n) i+1)).1).1,
    fun z hz => selected_disk_omitted C (cyclicSchedule m)
      (visitTime (L.subsequence n) i) z hz⟩

lemma RegularPhaseLimit.circle_subset_closure :
    sphere L.center L.radius⊆closure (L.map '' C.planeRegion) := by
  rw [←L.circle_image]
  rintro _ ⟨z,hz,rfl⟩
  have hzU := unit_circle_subset_symmetricCircleAnnulus P.radius_gt hz
  have hzfront : z∈frontier (closedBall (0:ℂ) 1) := by
    rw [frontier_closedBall (0:ℂ) one_ne_zero]
    exact hz
  have hzout : z∈closure {w:ℂ | 1<‖w‖} := by
    have he : (closedBall (0:ℂ) 1)ᶜ={w:ℂ | 1<‖w‖} := by
      ext w
      simp only [mem_compl_iff,mem_closedBall_zero_iff,mem_ofPred_eq,not_le]
    rw [frontier_eq_closure_inter_closure] at hzfront
    simpa only [he] using hzfront.2
  have hzcl : z∈closure (symmetricCircleAnnulus P.radius∩{w:ℂ | 1<‖w‖}) :=
    (isOpen_symmetricCircleAnnulus P.radius).inter_closure ⟨hzU,hzout⟩
  apply (((L.holomorphic z hzU).differentiableAt
    ((isOpen_symmetricCircleAnnulus P.radius).mem_nhds hzU)).continuousAt.continuousWithinAt).mem_closure hzcl
  intro w hw
  exact ⟨P.coordinate w,P.exterior_source w hw.1 hw.2,(L.agrees w hw.1 hw.2).symm⟩

lemma RegularPhaseLimit.circle_subset_frontier :
    sphere L.center L.radius⊆frontier (L.map '' C.planeRegion) := by
  rw [L.finite_map_properties.2.1.frontier_eq]
  intro z hz
  exact ⟨L.circle_subset_closure hz,L.omitted_disk (sphere_subset_closedBall hz)⟩

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
