import OAI.Analysis.CircleDomains.Transfer.CoreGeometry
import OAI.Analysis.CircleDomains.Topology.DiskRemainder

namespace OAI

/-!
# The safe region for filling after the terminals are selected

The remaining quotient dust is compact and relatively clopen. Its open
neighborhood is chosen to avoid both the retained physical core and all
closed terminal caps, so every later filling closure inherits both
separations.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def terminalRemainder {I : Type*} (π : Sphere → Sphere) (B : Set Sphere)
    (T : I → ℂ ≃ₜ ℂ) : Set Sphere := B \ (π '' sphericalDiskUnion T)

def closedTerminalImages {I : Type*} (π : Sphere → Sphere) (T : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  ⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (T i)))

theorem terminal_remainder_safe_region
    {I : Type*} [Fintype I] {G B C : Set Sphere} {π : Sphere → Sphere}
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hB : IsClosed B) (hBC : B ⊆ (π '' C)ᶜ) (hC : IsCompact C)
    (hinfty : OnePoint.infty ∈ C)
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O) :
    let A := terminalRemainder π B D.H
    let W := (π '' C)ᶜ ∩ (closedTerminalImages π D.H)ᶜ
    IsCompact A ∧ A ⊆ B ∧ IsClosed (B \ A) ∧ IsOpen W ∧ A ⊆ W ∧
      π OnePoint.infty ∉ A := by
  have hrem := compact_clopen_dust_remainder G π hπ hclosed hsurj hr D.H hB
    hB.isCompact (Subset.refl B) (by simp) D.frontier_good
  have hrem' : IsCompact (terminalRemainder π B D.H) ∧ terminalRemainder π B D.H ⊆ B ∧
      IsClosed (B \ terminalRemainder π B D.H) ∧
      Disjoint (terminalRemainder π B D.H) (closedTerminalImages π D.H) := by
    simpa only [terminalRemainder, sphericalDiskUnion, Set.image_iUnion, closedTerminalImages] using hrem
  have hclosedT : IsClosed (closedTerminalImages π D.H) :=
    isClosed_iUnion_of_finite (fun i =>
      (((isCompact_closure_jordanInterior (D.H i)).image OnePoint.continuous_coe).image hπ).isClosed)
  refine ⟨hrem'.1, hrem'.2.1, hrem'.2.2.1,
    (hC.image hπ).isClosed.isOpen_compl.inter hclosedT.isOpen_compl, ?_, ?_⟩
  · intro x hx
    exact ⟨hBC (hrem'.2.1 hx), Set.disjoint_left.mp hrem'.2.2.2 hx⟩
  · intro hx
    exact hBC (hrem'.2.1 hx) ⟨OnePoint.infty, hinfty, rfl⟩

theorem PhysicalTerminalDisks.index_mem_quotient_union
    {I : Type*} {G B : Set Sphere} {π : Sphere → Sphere} (hsurj : Surjective π)
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O)
    {i : I} (hi : p i ≠ π OnePoint.infty) : p i ∈ π '' sphericalDiskUnion D.H := by
  obtain ⟨x, hx⟩ := hsurj (p i)
  cases x using OnePoint.rec with
  | infty => exact (hi hx.symm).elim
  | coe z =>
    exact ⟨(z : Sphere), (coe_mem_sphericalDiskUnion D.H z).mpr
      ⟨i, D.fiber_subset i hx⟩, hx⟩

theorem PhysicalTerminalDisks.remainder_avoids_indices
    {I : Type*} {G B : Set Sphere} {π : Sphere → Sphere} (hsurj : Surjective π)
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O)
    (hp : ∀ i, p i ≠ π OnePoint.infty) :
    Disjoint (terminalRemainder π B D.H) (range p) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨i, rfl⟩
  exact hx.2 (D.index_mem_quotient_union hsurj (hp i))

/-- Every closed filling drawn in the safe region misses both the core
and every closed terminal cap. -/
theorem filling_closures_avoid_core_and_terminals
    {I J : Type*} {C : Set Sphere} {π : Sphere → Sphere}
    (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ)
    (hF : ∀ j, closure (jordanInterior (F j)) ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' ((π '' C)ᶜ ∩ (closedTerminalImages π T)ᶜ)) :
    (∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (F j))) C) ∧
      ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (F j))) := by
  constructor
  · intro j
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ hc
    exact (hF j hz).1 ⟨(z : Sphere), hc, rfl⟩
  · intro i j
    apply Set.disjoint_left.mpr
    intro z hzT hzF
    exact (hF j hzF).2 (mem_iUnion.mpr ⟨i, (z : Sphere), ⟨z, hzT, rfl⟩, rfl⟩)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
