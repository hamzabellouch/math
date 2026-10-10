import OAI.Analysis.CircleDomains.Transfer.SubordinateGraphCompletion
import OAI.Analysis.CircleDomains.Rigidity.LocalMaskNeighborhoods
import OAI.Analysis.CircleDomains.Transfer.SubordinateGraphFilling

namespace OAI

/-! The singularities of a finite masked list are retained as terminals.
Every remaining dust point therefore has a common real-branch neighborhood;
the filling caps can be chosen inside those actual neighborhoods. -/

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_mask_atlas_geometric_completion
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
    (hcompat : OrderedGraphGridCompatibility R θ N (terminalRemainder π B D.H) σ)
    (L : Fin n → Type*) (M : Fin n → Set Sphere) (hM : ∀ l, IsClosed (M l))
    (hboundary : ∀ l, frontier (M l) ⊆ Bᶜ)
    (singular : Fin n → S) (hflag : ∀ l, singular l ∈ F)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (hcover : ∀ l, M l \ {σ (singular l)} ⊆ ⋃ i, P l i) :
    ∃ (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      Pairwise (Disjoint on fun j => closure (jordanInterior (H j))) ∧
      (∀ i j, Disjoint (closure (jordanInterior (D.H i))) (closure (jordanInterior (H j)))) ∧
      (∀ j, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (H j))) C) ∧
      π ⁻¹' B ⊆ sphericalDiskUnion D.H ∪ sphericalDiskUnion H ∧
      C ⊆ completionCore D.H H ∧ completionCore D.H H ⊆ G ∧
      (∀ j, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ j) ∧ Topology.IsEmbedding (γ j) ∧
        frontier (jordanInterior (H j)) = range (γ j) ∧
        (∀ z ∈ frontier (jordanInterior (H j)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        (∃ k : ℕ, ∀ i : Fin n, i.val ≠ k →
          Disjoint (frontier (jordanInterior (H j)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ l, reciprocalGraphLevel (R i) (θ i) N l))) ∧
        ∀ l, Disjoint (closure (jordanInterior (H j)))
          ((fun z : ℂ => π (z : Sphere)) ⁻¹' M l) ∨
          ∃ i, closure (jordanInterior (H j)) ⊆
            (fun z : ℂ => π (z : Sphere)) ⁻¹' (interior (M l) ∩ P l i)) := by
  classical
  let : Fintype (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) := hfin.fintype
  have hBC : B ⊆ (π '' C)ᶜ := by
    rw [hBdef]
    exact (quotient_core_safe_open π hπ hC hCG hr).2.1
  have hpinf (s : gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) :
      σ s ≠ π OnePoint.infty := by
    intro heq
    exact hBC (hσB s) (heq ▸ (show π OnePoint.infty ∈ π '' C from
      ⟨OnePoint.infty, hinfty, rfl⟩))
  have hsingular (x : terminalRemainder π B D.H) (l : Fin n) :
      x.val ≠ σ (singular l) := by
    intro heq
    apply Set.disjoint_left.mp (D.remainder_avoids_indices hsurj hpinf) x.property
    exact ⟨⟨singular l, Or.inl (hflag l)⟩, heq.symm⟩
  have hlocal (x : terminalRemainder π B D.H) : ∃ V : Set Sphere,
      IsOpen V ∧ x.val ∈ V ∧ ∀ l,
        Disjoint V (M l) ∨ ∃ i, V ⊆ interior (M l) ∩ P l i :=
    exists_common_mask_branch_neighborhood L Bᶜ M hM hboundary
      (fun l => σ (singular l)) P hP hcover (by simpa using x.property.1) (hsingular x)
  choose V hV hxV hchoice using hlocal
  obtain ⟨m, H, γ, hHd, hDH, hHC, hcov, hCC, hCG', hcurves⟩ :=
    exists_subordinate_geometric_completion_for_graphs hsard hschoenflies
      G π hπ hclosed hsurj hr hB hBdef hTD hC hCG hinfty R hR σ hσB a b θ F
      hband hfin O D hDcore hfree hcompat V hV hxV
  refine ⟨m, H, γ, hHd, hDH, hHC, hcov, hCC, hCG', ?_⟩
  intro j
  obtain ⟨hj, he, hb, hg, hgrid, x, hx⟩ := hcurves j
  refine ⟨hj, he, hb, hg, hgrid, fun l => ?_⟩
  rcases hchoice x l with hd | ⟨i, hi⟩
  · left
    apply Set.disjoint_left.mpr
    intro z hz hm
    exact Set.disjoint_left.mp hd (hx hz) hm
  · exact Or.inr ⟨i, fun z hz => hi (hx hz)⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
