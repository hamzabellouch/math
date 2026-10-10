import OAI.Analysis.CircleDomains.Topology.GraphFillingDisks
import OAI.Analysis.CircleDomains.Transfer.GeometricCompletion

namespace OAI

/-! Cover the remaining quotient dust using the actual closed level
sets of mixed real and period tests, after the physical collision
terminals have been selected. -/

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_geometric_completion_for_graphs
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B C : Set Sphere} (hB : IsClosed B) (hBdef : B = π '' Gᶜ)
    (hTD : IsTotallyDisconnected B) (hC : IsCompact C) (hCG : C ⊆ G)
    (hinfty : OnePoint.infty ∈ C)
    {n N : ℕ} {S : Type*} (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (σ : S → Sphere) (hσB : ∀ s, σ s ∈ B)
    (a b : Fin n → S → ℝ) (θ : Fin n → ℝ) (F : Set S)
    (hband : ∀ i s, {t : UnitAddCircle | (σ s, t) ∈ R i} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a i s) (b i s))
    (hfin : (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite)
    (O : (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) → Set Sphere)
    (D : PhysicalTerminalDisks G π B (fun s : gridTerminalIndices F (reciprocalGridStep N)
      upperPair a b θ => σ s) O)
    (hDcore : ∀ i, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (D.H i))) C)
    (hfree : ∀ x ∈ terminalRemainder π B D.H, x ∉ range σ → ∀ i,
      {t : UnitAddCircle | (x, t) ∈ R i}.Subsingleton)
    (hcompat : OrderedGraphGridCompatibility R θ N (terminalRemainder π B D.H) σ) :
    ∃ (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      Pairwise (Disjoint on fun j => closure (jordanInterior (H j))) ∧
      (∀ i j, Disjoint (closure (jordanInterior (D.H i))) (closure (jordanInterior (H j)))) ∧
      (∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (H j))) C) ∧
      π ⁻¹' B ⊆ sphericalDiskUnion D.H ∪ sphericalDiskUnion H ∧
      C ⊆ completionCore D.H H ∧ completionCore D.H H ⊆ G ∧
      (∀ j, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ j) ∧ Topology.IsEmbedding (γ j) ∧
        frontier (jordanInterior (H j)) = range (γ j) ∧
        (∀ z ∈ frontier (jordanInterior (H j)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        ∃ k : ℕ, ∀ i : Fin n, i.val ≠ k →
          Disjoint (frontier (jordanInterior (H j)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ l, reciprocalGraphLevel (R i) (θ i) N l))) := by
  classical
  let : Fintype (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) := hfin.fintype
  have hBC : B ⊆ (π '' C)ᶜ := by
    rw [hBdef]
    exact (quotient_core_safe_open π hπ hC hCG hr).2.1
  obtain ⟨hA, hAB, hBA, hW, hAW, hAinf⟩ :=
    terminal_remainder_safe_region hπ hclosed hsurj hr hB hBC hC hinfty D
  have hpinf (s : gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) :
      σ s ≠ π OnePoint.infty := by
    intro heq
    exact hBC (hσB s) (heq ▸ (show π OnePoint.infty ∈ π '' C from
      ⟨OnePoint.infty, hinfty, rfl⟩))
  have hnoterm : Disjoint (terminalRemainder π B D.H)
      (σ '' gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨s, hs, hσ⟩
    exact Set.disjoint_left.mp (D.remainder_avoids_indices hsurj hpinf) hx ⟨⟨s, hs⟩, hσ⟩
  obtain ⟨m, H, γ, hcover, hdisj, hcurves⟩ := exists_filling_disks_of_compatible_graphs
    hsard hschoenflies G π hπ hclosed hsurj hr R hR σ a b θ
    upperPair upperPair_covers F hband hB hTD hA hAB hBA hW hAW hAinf
    (fun x hx => hBdef.symm ▸ (show π x ∈ π '' Gᶜ from ⟨x, hx, rfl⟩))
    hnoterm hfree hcompat
  have hsafe := filling_closures_avoid_core_and_terminals D.H H
    (fun j => (hcurves j).1)
  have hfill := spherical_remainder_cover_of_physical_cover D.H H B π hAinf hcover
  have htotal := dust_preimage_covered_of_remainder_cover D.H H G B π hsurj hr
    (fun i z hz => (D.frontier_good i z hz).1) hfill
  refine ⟨m, H, γ, hdisj, hsafe.2, hsafe.1, htotal, ?_,
    completionCore_subset_domain D.H H G B π
      (fun x hx => hBdef.symm ▸ (show π x ∈ π '' Gᶜ from ⟨x, hx, rfl⟩)) htotal, ?_⟩
  · intro x hx hbad
    rcases hbad with ht | hf
    · obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp ht
      exact Set.disjoint_left.mp (hDcore i) ⟨z, subset_closure hz, rfl⟩ hx
    · obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp hf
      exact Set.disjoint_left.mp (hsafe.1 j) ⟨z, subset_closure hz, rfl⟩ hx
  · intro j
    exact (hcurves j).2

end CircleDomainRigidity.FiniteTransfer

end

end OAI
