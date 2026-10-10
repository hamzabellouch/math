import OAI.Analysis.CircleDomains.Transfer.SourceTargetEnds

namespace OAI

/-!
# Trapping a corresponding component by any retained contour

The source end need only lie inside the chosen contour. Compactness places
a sufficiently late source collar there, and the matched side equality
places its target collar inside the target contour.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem SmoothJordanCore.omitted_point_mem_side
    {G : Set Sphere} (A : SmoothJordanCore G) {q : Sphere} (hq : q ∈ Gᶜ)
    {j : Fin A.count} (hqj : q ∈ closedTerminalCap (A.disk j)) :
    q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) := by
  have hnot : q ∉ A.carrier := fun h => hq (A.subset h)
  have hqunion : q ∈ ⋃ k, ((↑) : ℂ → Sphere) '' jordanInterior (A.disk k) :=
    not_not.mp hnot
  obtain ⟨k, z, hz, he⟩ := mem_iUnion.mp hqunion
  by_cases hkj : k = j
  · exact hkj ▸ ⟨z, hz, he⟩
  · exact (Set.disjoint_left.mp (disjoint_closedTerminalCaps A.disk A.disjoint hkj)
      ⟨z, subset_closure hz, he⟩ hqj).elim

theorem matched_component_subset_retained_side
    {G : Set Sphere} {f : Sphere → Sphere}
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (b : (n : ℕ) → Fin (C n).count)
    (hsourceNest : Antitone (fun n => closedTerminalCap ((C n).disk (b n))))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    {S E : Set Sphere}
    (hsource : S = ⋂ n, closedTerminalCap ((C n).disk (b n)))
    (htarget : E = ⋂ n, closedTerminalCap (J n (b n)))
    (H L : ℂ ≃ₜ ℂ)
    (hside : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior L))
    (hS : S ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H) :
    E ⊆ ((↑) : ℂ → Sphere) '' jordanInterior L := by
  obtain ⟨n, hn⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap ((C n).disk (b n))).isClosed)
    hsourceNest (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)) (hsource ▸ hS)
  have hfrontG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk (b n))) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hxf : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨b n, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hxf
  have hfront : frontier (jordanInterior (J n (b n))) ⊆ jordanInterior L := by
    intro z hz
    have hzimage : (z : Sphere) ∈
        f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk (b n)))) := by
      rw [hboundary n (b n)]
      exact mem_image_of_mem _ hz
    obtain ⟨x, hx, hxe⟩ := hzimage
    have hxcap : x ∈ closedTerminalCap ((C n).disk (b n)) := by
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, frontier_subset_closure hw, rfl⟩
    have hzside : (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior L := by
      have hmem : (z : Sphere) ∈ f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) :=
        ⟨x, ⟨hfrontG hx, hn hxcap⟩, hxe⟩
      rw [hside] at hmem
      exact hmem.2
    exact OnePoint.coe_injective.mem_set_image.mp hzside
  rw [htarget]
  exact (iInter_subset _ n).trans
    (image_mono (closed_jordanInterior_subset_of_frontier_subset (J n (b n)) L hfront))

end CircleDomainRigidity

end

end OAI
