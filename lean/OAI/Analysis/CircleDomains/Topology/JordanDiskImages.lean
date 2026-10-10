import OAI.Analysis.CircleDomains.Topology.ImageCoreJordan

namespace OAI

/-! Compact Jordan disks contained in the domain of an open embedding have their actual Jordan
interiors as images. This identifies the anchor disks in finite models. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

private theorem planar_interior_image
    {f : ℂ → ℂ} {G K : Set ℂ} (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hG : IsOpen G)
    (hi : InjOn f G) (hKG : K ⊆ G) : interior (f '' K) = f '' interior K := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := interior_subset hy
    have hO : IsOpen (G ∩ f ⁻¹' interior (f '' K)) :=
      hc.isOpen_inter_preimage hG isOpen_interior
    have hsub : G ∩ f ⁻¹' interior (f '' K) ⊆ K := by
      rintro z ⟨hzG, hz⟩
      obtain ⟨w, hw, he⟩ := interior_subset hz
      exact (hi (hKG hw) hzG he) ▸ hw
    exact ⟨x, interior_maximal hsub hO ⟨hKG hx, hy⟩, rfl⟩
  · exact interior_maximal (image_mono interior_subset)
      (ho _ isOpen_interior (interior_subset.trans hKG))

private theorem planar_frontier_image
    {f : ℂ → ℂ} {G K : Set ℂ} (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hG : IsOpen G)
    (hi : InjOn f G) (hK : IsCompact K) (hKG : K ⊆ G) :
    frontier (f '' K) = f '' frontier K := by
  have hfc : IsClosed (f '' K) := (hK.image_of_continuousOn (hc.mono hKG)).isClosed
  rw [frontier, hfc.closure_eq, planar_interior_image hc ho hG hi hKG,
    frontier, hK.isClosed.closure_eq]
  exact ((hi.mono hKG).image_sdiff_subset interior_subset).symm

private theorem open_eq_jordan_of_frontier
    (H : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hne : U.Nonempty) (hf : frontier U = frontier (jordanInterior H)) :
    U = jordanInterior H := by
  have hsub : U ⊆ jordanInterior H := by
    have ht := open_subset_finite_jordanInteriors_of_frontier_subset (fun _ : Unit => H)
      (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim) hU hb
      (by simpa only [iUnion_const, hf] using frontier_subset_closure)
      (fun _ => hf.symm.subset)
    simpa only [iUnion_const] using ht
  apply Subset.antisymm hsub
  apply (isConnected_jordanInterior H).isPreconnected.subset_of_closure_inter_subset hU
  · obtain ⟨z, hz⟩ := hne
    exact ⟨z, hsub hz, hz⟩
  · rintro z ⟨hzcl, hzH⟩
    by_contra hzU
    have hzF : z ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hzcl, hzU⟩
    rw [hf, (jordanInterior_isOpen H).frontier_eq] at hzF
    exact hzF.2 hzH

/-- An open bounded region with the boundary of a Jordan disk is that disk. -/
theorem open_eq_jordanInterior_of_frontier
    (H : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hne : U.Nonempty) (hf : frontier U = frontier (jordanInterior H)) :
    U = jordanInterior H := open_eq_jordan_of_frontier H hU hb hne hf

/-- The images are the whole Jordan interior and its closure, rather than merely subsets of the
corresponding sides, by planar Schoenflies. -/
theorem exists_jordan_image_disk (hsch : PlanarSchoenflies)
    {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ G) :
    ∃ K : ℂ ≃ₜ ℂ,
      f '' jordanInterior H = jordanInterior K ∧
      f '' closure (jordanInterior H) = closure (jordanInterior K) ∧
      frontier (jordanInterior K) = f '' frontier (jordanInterior H) := by
  let γ : Circle → ℂ := fun t => H t
  have hγ : Continuous γ := H.continuous.comp continuous_subtype_val
  have hγH (t : Circle) : γ t ∈ frontier (jordanInterior H) := by
    rw [frontier_jordanInterior]
    exact ⟨t, t.property, rfl⟩
  have hγG (t : Circle) : γ t ∈ G := hHG (frontier_subset_closure (hγH t))
  have hδ : Continuous (f ∘ γ) := hc.comp_continuous hγ hγG
  have hδinj : Injective (f ∘ γ) := by
    intro s t he
    apply Subtype.ext
    apply H.injective
    exact hi (hγG s) (hγG t) he
  obtain ⟨K, hK⟩ := hsch (f ∘ γ) hδ hδinj
  have hrange : range γ = frontier (jordanInterior H) := by
    rw [frontier_jordanInterior]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hfront : frontier (jordanInterior K) = f '' frontier (jordanInterior H) := by
    rw [frontier_jordanInterior_eq_circle_range K (f ∘ γ) hK, range_comp, hrange]
  let P := closure (jordanInterior H)
  have hPc : IsCompact P := isCompact_closure_jordanInterior H
  have hPi : interior P = jordanInterior H := interior_closure_jordanInterior H
  have hPfront : frontier P = frontier (jordanInterior H) := by
    simp only [frontier, P, closure_closure, interior_closure_jordanInterior,
      (jordanInterior_isOpen H).interior_eq]
  have hiimage : interior (f '' P) = f '' jordanInterior H := by
    rw [planar_interior_image hc ho hG hi hHG, hPi]
  have hreg : closure (f '' jordanInterior H) = f '' P := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono subset_closure)
        (hPc.image_of_continuousOn (hc.mono hHG)).isClosed
    · exact (hc.mono hHG).image_closure
  have himagefront : frontier (f '' jordanInterior H) = frontier (jordanInterior K) := by
    rw [frontier, hreg, (ho _ (jordanInterior_isOpen H) (subset_closure.trans hHG)).interior_eq]
    rw [← hiimage]
    have he := planar_frontier_image hc ho hG hi hPc hHG
    rw [hPfront, ← hfront] at he
    simpa only [frontier, (hPc.image_of_continuousOn (hc.mono hHG)).isClosed.closure_eq] using he
  have himage : f '' jordanInterior H = jordanInterior K :=
    open_eq_jordan_of_frontier K (ho _ (jordanInterior_isOpen H) (subset_closure.trans hHG))
      ((hPc.image_of_continuousOn (hc.mono hHG)).isBounded.subset (image_mono subset_closure))
      ((isConnected_jordanInterior H).nonempty.image f) himagefront
  exact ⟨K, himage, by rw [← hreg, himage], hfront⟩

end CircleDomainRigidity

end

end OAI
