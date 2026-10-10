import OAI.Analysis.CircleDomains.Rigidity.MaskAtlasGeometricCompletion
import OAI.Analysis.CircleDomains.Transfer.RetainedTerminalGeometry

namespace OAI

/-! Assemble physical collision terminals and the remaining filling
contours for a mixed finite list. Nonsingular local real branches give
terminal bounds; closed level graphs give the filling geometry. -/

open Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

attribute [local instance] sphereMetric

 theorem exists_mask_atlas_geometric_assembly
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (hG : IsOpen G) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    (C : Set Sphere) (hC : IsCompact C) (hCG : C ⊆ G) (hinfty : OnePoint.infty ∈ C)
    {n N : ℕ} {S : Type*}
    (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ l, IsClosed (R l))
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (a b : Fin n → S → ℝ) (θ : Fin n → ℝ) (Flag : Set S)
    (hband : ∀ l s, {t : UnitAddCircle | (σ s, t) ∈ R l} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a l s) (b l s))
    (hfin : (gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ).Finite)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    (U : S → Set Sphere) (v : S → Fin n → Sphere → ℝ) (M : S → Fin n → ℝ)
    (hbounded : ∀ s l x, x ∈ U s → |v s l x| ≤ M s l)
    (hphysical : ∀ s (z : ℂ), (z : Sphere) ∈ G → π (z : Sphere) ∈ O s →
      π (z : Sphere) ∈ U s)
    (active : S → Fin n → Prop)
    (hbudget : ∀ s l, active s l →
      limsup (v s l) (𝓝[U s] (σ s)) - liminf (v s l) (𝓝[U s] (σ s)) ≤ b l s - a l s)
    (hfree : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l,
      {t : UnitAddCircle | (x, t) ∈ R l}.Subsingleton)
    (hcompat : OrderedGraphGridCompatibility R θ N (π '' Gᶜ) σ)
    (L : Fin n → Type*) (Mask : Fin n → Set Sphere) (hMask : ∀ l, IsClosed (Mask l))
    (hboundary : ∀ l, frontier (Mask l) ⊆ (π '' Gᶜ)ᶜ)
    (singular : Fin n → S) (hflag : ∀ l, singular l ∈ Flag)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (hcover : ∀ l, Mask l \ {σ (singular l)} ⊆ ⋃ i, P l i) :
    ∃ (D : PhysicalTerminalDisks G π (π '' Gᶜ)
        (fun s : gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ => σ s)
        (fun s => O s))
      (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      (∀ s, Disjoint (closedTerminalCap (D.H s)) C) ∧
      C ⊆ openCompletedRegion D.H ∧
      (∀ (s : gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ) l,
        active s l → ∀ δ η : ℝ,
        ∀ x ∈ frontier (jordanInterior (D.H s)),
        ∀ y ∈ frontier (jordanInterior (D.H s)),
        |shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (x : Sphere))) -
          shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (y : Sphere)))| ≤
            (b l s - a l s) + 4 * reciprocalGridStep N) ∧
      Pairwise (Disjoint on fun j => closure (jordanInterior (H j))) ∧
      (∀ s j, Disjoint (closure (jordanInterior (D.H s))) (closure (jordanInterior (H j)))) ∧
      (∀ j, Disjoint (closedTerminalCap (H j)) C) ∧
      π ⁻¹' (π '' Gᶜ) ⊆ sphericalDiskUnion D.H ∪ sphericalDiskUnion H ∧
      C ⊆ completionCore D.H H ∧ completionCore D.H H ⊆ G ∧
      (∀ j, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ j) ∧ Topology.IsEmbedding (γ j) ∧
        frontier (jordanInterior (H j)) = range (γ j) ∧
        (∀ z ∈ frontier (jordanInterior (H j)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ π '' Gᶜ) ∧
        (∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
          Disjoint (frontier (jordanInterior (H j)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ r, reciprocalGraphLevel (R l) (θ l) N r))) ∧
        ∀ l, Disjoint (closure (jordanInterior (H j)))
          ((fun z : ℂ => π (z : Sphere)) ⁻¹' Mask l) ∨
          ∃ i, closure (jordanInterior (H j)) ⊆
            (fun z : ℂ => π (z : Sphere)) ⁻¹' (interior (Mask l) ∩ P l i)) := by
  let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ
  let : Fintype A := hfin.fintype
  obtain ⟨D, hD, hCQ, hosc⟩ := exists_retained_physical_terminals_with_staircase_bound
    hsard hsch hG hC hCG hinfty π hπ hclosed hsurj hr hTD
    (fun s : A => σ s) (hσ.comp Subtype.val_injective) (fun s => hσB s)
    (fun s => O s) (fun s => hO s) (fun s => U s) (fun s => v s) (fun s => M s)
    (fun s => hbounded s) (fun s => hphysical s) (fun s => active s)
    (fun s l => b l s - a l s) (fun s => hbudget s) (reciprocalGridStep_pos N)
  obtain ⟨m, H, γ, hHd, hDH, hHC, hcover, hCC, hCG', hcurves⟩ :=
    exists_mask_atlas_geometric_completion hsard hsch G π hπ hclosed hsurj hr
      (hG.isClosed_compl.isCompact.image hπ).isClosed rfl hTD hC hCG hinfty
      R hR σ hσB a b θ Flag hband hfin (fun s => O s) D hD
      (fun x hx => hfree x hx.1) (fun x hx => hcompat x hx.1)
      L Mask hMask hboundary singular hflag P hP hcover
  exact ⟨D, m, H, γ, hD, hCQ, hosc, hHd, hDH, hHC, hcover, hCC, hCG', hcurves⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
