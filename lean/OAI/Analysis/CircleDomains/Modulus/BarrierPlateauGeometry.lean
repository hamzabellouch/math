import OAI.Analysis.CircleDomains.Topology.PhysicalPlaneCoordinates
import Mathlib.Topology.Separation.Regular

namespace OAI

/-! The compact exterior and relatively closed plateau sets used when
smoothing the filled first-arrival barrier. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_compact_plane_exterior_of_nhds
    {V : Set Sphere} (hV : V ∈ 𝓝 OnePoint.infty) :
    ∃K : Set EuclideanPlane, IsCompact K ∧ ∀x ∉ K, planeSphere x ∈ V := by
  obtain ⟨S, ⟨_, hS⟩, hSV⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hV
  refine ⟨complexPlaneCoordinates.symm '' S, hS.image complexPlaneCoordinates.symm.continuous, ?_⟩
  intro x hx
  apply hSV
  left
  refine ⟨complexPlaneCoordinates x, ?_, rfl⟩
  intro hz
  exact hx ⟨complexPlaneCoordinates x, hz, complexPlaneCoordinates.symm_apply_apply x⟩

theorem physical_plateau_relative_complement_open
    {X : Type*} [TopologicalSpace X] {G : Set Sphere} (hG : IsOpen G)
    {π : Sphere → X} (hπ : Continuous π) {A : Set X} (hA : IsClosed A) :
    IsOpen (physicalPlaneDomain G \
      (physicalPlaneDomain G ∩ (π ∘ planeSphere) ⁻¹' A)) := by
  have heq : physicalPlaneDomain G \
      (physicalPlaneDomain G ∩ (π ∘ planeSphere) ⁻¹' A) =
      physicalPlaneDomain G ∩ (π ∘ planeSphere) ⁻¹' Aᶜ := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_compl_iff]
    tauto
  rw [heq]
  exact (isOpen_physicalPlaneDomain hG).inter (hA.isOpen_compl.preimage
    (hπ.comp continuous_planeSphere))

theorem exists_closed_anchor_plateau
    {X : Type*} [TopologicalSpace X] [RegularSpace X]
    {E F : Set X} (hF : IsCompact F) (hFE : F ⊆ interior E) :
    ∃A V : Set X, IsClosed A ∧ IsOpen V ∧ F ⊆ interior A ∧ A ⊆ V ∧ V ⊆ E := by
  obtain ⟨U, hU, hFU, hUE⟩ := hF.exists_isOpen_closure_subset
    (isOpen_interior.mem_nhdsSet.mpr hFE)
  refine ⟨closure U, interior E, isClosed_closure, isOpen_interior, ?_, hUE, interior_subset⟩
  exact hFU.trans (hU.subset_interior_closure)

end CircleDomainRigidity

end

end OAI
