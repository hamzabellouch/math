import OAI.Analysis.CircleDomains.Uniformization.FiniteModelEnds

namespace OAI

/-!
# Retained cores localize every marked terminal

A connected terminal disk disjoint from a retained core lies in one of
that core's holes. A point of the terminal identifies which hole it is.
Thus retaining the core and retaining a mark already imply the physical
containment needed for the target trapping argument.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem terminal_subset_retained_side
    {I : Type*} (T : I → ℂ ≃ₜ ℂ) {G : Set Sphere} (A : SmoothJordanCore G)
    (hret : A.carrier ⊆ openCompletedRegion T)
    {i : I} {q : Sphere} (hq : q ∈ closedTerminalCap (T i))
    {j : Fin A.count} (hqside : q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j)) :
    closedTerminalCap (T i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) := by
  have hopenCover : closedTerminalCap (T i) ⊆
      ⋃ k, ((↑) : ℂ → Sphere) '' jordanInterior (A.disk k) := by
    intro x hx
    have hnot : x ∉ A.carrier := by
      intro hxa
      exact hret hxa (mem_iUnion.mpr ⟨i, hx⟩)
    exact not_not.mp hnot
  have hclosedCover : closedTerminalCap (T i) ⊆ ⋃ k, closedTerminalCap (A.disk k) := by
    intro x hx
    obtain ⟨k, z, hz, he⟩ := mem_iUnion.mp (hopenCover hx)
    exact mem_iUnion.mpr ⟨k, z, subset_closure hz, he⟩
  have hqcap : q ∈ closedTerminalCap (A.disk j) := by
    obtain ⟨z, hz, he⟩ := hqside
    exact ⟨z, subset_closure hz, he⟩
  have hpiece := connectedComponentIn_subset_finite_closed_piece
    (fun k => closedTerminalCap (A.disk k))
    (fun k => (isCompact_closedTerminalCap (A.disk k)).isClosed)
    (disjoint_closedTerminalCaps A.disk A.disjoint) hclosedCover hq hqcap
  have hTi := (isPreconnected_closedTerminalCap (T i)).subset_connectedComponentIn hq (Subset.refl _)
  intro x hx
  have hxj := hpiece (hTi hx)
  obtain ⟨k, z, hz, he⟩ := mem_iUnion.mp (hopenCover hx)
  by_cases hkj : k = j
  · exact hkj ▸ ⟨z, hz, he⟩
  · exact (Set.disjoint_left.mp (disjoint_closedTerminalCaps A.disk A.disjoint hkj)
      ⟨z, subset_closure hz, he⟩ hxj).elim

end CircleDomainRigidity

end

end OAI
