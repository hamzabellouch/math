import OAI.Analysis.CircleDomains.Topology.QuotientDiskTopology

namespace OAI

/-!
# Dust remaining after a finite contour family

When the physical boundaries miss the dust, removing the interiors of a
finite family leaves compact relatively clopen dust disjoint from every
closed fill. This supplies the invariant for the descending grid stages.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem quotient_cover_of_physical_cover
    {I X : Type*} (π : Sphere → X) (hsurj : Surjective π)
    (U : I → Set ℂ) {A : Set X} (hinfty : π OnePoint.infty ∉ A)
    (hcover : (fun z : ℂ => π (z : Sphere)) ⁻¹' A ⊆ ⋃ i, U i) :
    A ⊆ ⋃ i, π '' (((↑) : ℂ → Sphere) '' U i) := by
  intro x hx
  obtain ⟨p, rfl⟩ := hsurj x
  cases p using OnePoint.rec with
  | infty => exact (hinfty hx).elim
  | coe z =>
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨i, _, ⟨z, hi, rfl⟩, rfl⟩

theorem dust_inter_closed_fills_eq_inter_interiors
    {I X : Type*} (π : Sphere → X) (H : I → ℂ ≃ₜ ℂ) {B : Set X}
    (hboundary : ∀ i z, z ∈ frontier (jordanInterior (H i)) → π (z : Sphere) ∉ B) :
    B ∩ (⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (H i)))) =
      B ∩ (⋃ i, π '' (((↑) : ℂ → Sphere) '' jordanInterior (H i))) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxB, hx⟩
    obtain ⟨i, p, hp, hpx⟩ := mem_iUnion.mp hx
    obtain ⟨z, hz, rfl⟩ := hp
    have hzU : z ∈ jordanInterior (H i) := by
      by_contra hzU
      have hzfront : z ∈ frontier (jordanInterior (H i)) := by
        rw [(jordanInterior_isOpen (H i)).frontier_eq]
        exact ⟨hz, hzU⟩
      exact hboundary i z hzfront (hpx.symm ▸ hxB)
    exact ⟨hxB, mem_iUnion.mpr ⟨i, _, ⟨z, hzU, rfl⟩, hpx⟩⟩
  · exact inter_subset_inter_right _ (iUnion_mono fun _ => image_mono (image_mono subset_closure))

theorem compact_clopen_dust_remainder
    {I : Type*} [Finite I]
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : I → ℂ ≃ₜ ℂ) {B A : Set Sphere} (hB : IsClosed B)
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hboundary : ∀ i z, z ∈ frontier (jordanInterior (H i)) →
      (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) :
    let U := ⋃ i, π '' (((↑) : ℂ → Sphere) '' jordanInterior (H i))
    let C := ⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (H i)))
    IsCompact (A \ U) ∧ (A \ U) ⊆ B ∧ IsClosed (B \ (A \ U)) ∧ Disjoint (A \ U) C := by
  dsimp only
  let U := ⋃ i, π '' (((↑) : ℂ → Sphere) '' jordanInterior (H i))
  let C := ⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (H i)))
  have hU : IsOpen U := isOpen_iUnion fun i =>
    isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr (H i)
      (fun z hz => (hboundary i z hz).1)
  have hC : IsClosed C := isClosed_iUnion_of_finite fun i =>
    (((isCompact_closure_jordanInterior (H i)).image OnePoint.continuous_coe).image hπ).isClosed
  have heq : B ∩ C = B ∩ U :=
    dust_inter_closed_fills_eq_inter_interiors π H (fun i z hz => (hboundary i z hz).2)
  have hdiff : B \ (A \ U) = (B \ A) ∪ (B ∩ C) := by
    rw [heq]
    ext x
    simp only [mem_sdiff, mem_union, mem_inter_iff]
    tauto
  refine ⟨hA.diff hU, (fun _ hx => hAB hx.1), ?_, ?_⟩
  · rw [hdiff]
    exact hBA.union (hB.inter hC)
  · apply Set.disjoint_left.mpr
    intro x hx hxC
    have hxU : x ∈ B ∩ U := heq ▸ ⟨hAB hx.1, hxC⟩
    exact hx.2 hxU.2

theorem remainder_avoids_covered_set
    {X : Type*} {A J U : Set X} (hcover : A ∩ J ⊆ U) :
    Disjoint (A \ U) J := by
  exact Set.disjoint_left.mpr fun _ hx hxJ => hx.2 (hcover ⟨hx.1, hxJ⟩)

end CircleDomainRigidity

end OAI
