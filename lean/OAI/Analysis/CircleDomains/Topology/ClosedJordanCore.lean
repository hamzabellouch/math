import OAI.Analysis.CircleDomains.Uniformization.FiniteCompletionUniformization

namespace OAI

/-!
# Closed cores bounded by a finite disjoint Jordan family

The closed common exterior is regular closed, its interior is the already
constructed connected open completed region, and its boundary is exactly
the union of the specified Jordan curves.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def closedJordanCore {I : Type*} (H : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  (⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i))ᶜ

theorem interior_finite_disjoint_closed
    {I : Type*} [Finite I] (C : I → Set Sphere)
    (hC : ∀ i, IsClosed (C i)) (hd : Pairwise (Disjoint on C)) :
    interior (⋃ i, C i) = ⋃ i, interior (C i) := by
  classical
  apply Subset.antisymm
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hp)
    let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, C j
    have hB : IsClosed B := isClosed_iUnion_of_finite fun j => hC j
    have hpB : p ∉ B := by
      intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact Set.disjoint_left.mp (hd j.property.symm) hi hj
    have hsub : interior (⋃ j, C j) ∩ Bᶜ ⊆ C i := by
      rintro q ⟨hq, hqB⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hq)
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact (hqB (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
    exact mem_iUnion.mpr ⟨i, interior_maximal hsub (isOpen_interior.inter hB.isOpen_compl) ⟨hp, hpB⟩⟩
  · exact iUnion_subset fun i => interior_mono (subset_iUnion C i)

theorem interior_closedTerminalCap (H : ℂ ≃ₜ ℂ) :
    interior (closedTerminalCap H) = ((↑) : ℂ → Sphere) '' jordanInterior H := by
  ext p
  cases p using OnePoint.rec with
  | infty =>
    have hnot : OnePoint.infty ∉ closedTerminalCap H := by
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
    simp only [OnePoint.infty_notMem_image_coe, iff_false]
    exact fun h => hnot (interior_subset h)
  | coe z =>
    change z ∈ ((↑) : ℂ → Sphere) ⁻¹' interior (closedTerminalCap H) ↔ _
    rw [OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
      OnePoint.continuous_coe]
    simp only [closedTerminalCap, OnePoint.coe_injective.preimage_image,
      interior_closure_jordanInterior, OnePoint.coe_injective.mem_set_image]

theorem interior_closedJordanCore {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ) :
    interior (closedJordanCore H) = openCompletedRegion H := by
  rw [closedJordanCore, interior_compl, closure_iUnion_of_finite]
  simp only [closure_sphere_image_jordanInterior]
  rfl

theorem closure_interior_closedJordanCore
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    closure (interior (closedJordanCore H)) = closedJordanCore H := by
  rw [interior_closedJordanCore, openCompletedRegion, closure_compl,
    interior_finite_disjoint_closed (fun i => closedTerminalCap (H i))
      (fun i => (isCompact_closedTerminalCap (H i)).isClosed) (disjoint_closedTerminalCaps H hd)]
  simp only [interior_closedTerminalCap, closedJordanCore]

theorem frontier_closedJordanCore
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    frontier (closedJordanCore H) =
      ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := by
  rw [closedJordanCore, frontier_compl]
  have hUo : IsOpen (⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i)) :=
    isOpen_iUnion fun i => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H i))
  rw [hUo.frontier_eq, closure_iUnion_of_finite]
  simp only [closure_sphere_image_jordanInterior]
  apply Subset.antisymm
  · rintro p ⟨hp, hnot⟩
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hp
    refine mem_iUnion.mpr ⟨i, z, ?_, rfl⟩
    rw [(jordanInterior_isOpen (H i)).frontier_eq]
    exact ⟨hz, fun hi => hnot (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)⟩
  · intro p hp
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hp
    refine ⟨mem_iUnion.mpr ⟨i, z, frontier_subset_closure hz, rfl⟩, ?_⟩
    intro hi
    obtain ⟨j, w, hw, he⟩ := mem_iUnion.mp hi
    have hwz : w = z := OnePoint.coe_injective he
    subst w
    by_cases hij : i = j
    · subst j
      exact hz.2 ((jordanInterior_isOpen (H i)).interior_eq.symm ▸ hw)
    · exact Set.disjoint_left.mp (hd hij) (frontier_subset_closure hz) (subset_closure hw)

end CircleDomainRigidity

end

end OAI
