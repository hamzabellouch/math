import OAI.Analysis.CircleDomains.Rigidity.MaskAtlasGeometricAssembly
import OAI.Analysis.CircleDomains.Rigidity.MaskAtlasGeometricCompletion
import OAI.Analysis.CircleDomains.Transfer.RetainedTerminalGeometry
import OAI.Analysis.CircleDomains.Rigidity.MaskedGridPreparation

namespace OAI

/-! Select one regular core, cutoff and reciprocal grid for the actual
finite masked list, then construct its terminal and subordinate filling
caps using that very grid. All cost and terminal estimates retain these
same choices. -/

open Set Function Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

attribute [local instance] sphereMetric

 theorem exists_prepared_mask_atlas_geometry
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (hG : IsOpen G) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    (hinfty : OnePoint.infty ∈ G)
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {n : ℕ} {S : Type*} [Countable S]
    (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ l, IsClosed (R l))
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (a b : Fin n → S → ℝ) (Flag : Set S) (hFlag : Flag.Finite)
    (hwidth : ∀ l s, 0 ≤ b l s - a l s)
    (hwidth2 : ∀ l, Summable (fun s => (b l s - a l s) ^ 2))
    (hband : ∀ l s, {t : UnitAddCircle | (σ s, t) ∈ R l} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a l s) (b l s))
    (Mm : Fin n → Set (ℝ × ℝ)) (hMm : ∀ l, MeasurableSet (Mm l))
    (hMmB : ∀ l, frontier (Mm l) ⊆ realChartDomain G)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (realChartDomain G ∩ interior (Mm l)))
    (hmf : ∀ l, Measurable (f l)) (hdf : ∀ l, Measurable (circleGradient (f l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2 ((volume.restrict (realChartDomain G)).restrict (Mm l)))
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
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (R j) R labels) = 0)
    (L : Fin n → Type*) (Mask : Fin n → Set Sphere) (hMask : ∀ l, IsClosed (Mask l))
    (hboundary : ∀ l, frontier (Mask l) ⊆ (π '' Gᶜ)ᶜ)
    (singular : Fin n → S) (hflag : ∀ l, singular l ∈ Flag)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (hcover : ∀ l, Mask l \ {σ (singular l)} ⊆ ⋃ i, P l i)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ (K : Set (ℝ × ℝ)) (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ),
      IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ realChartDomain G ∧ IsCompact (closure Kᶜ) ∧
      (∀ l, frontier (Mm l) ⊆ interior K) ∧
      ContDiff ℝ ∞ χ ∧ (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧
      (∀ᶠ z in 𝓝ˢ (realChartDomain G)ᶜ, χ z = 1) ∧ reciprocalGridStep N < ρ ∧
      (gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ).ncard : ℝ) < η ∧
      (∀ k, IntegrableOn (maskedCircleWedges Mm (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ)) (realChartDomain G \ K)) ∧
      (∃ᶠ k in atTop, (∫ z in realChartDomain G \ K, maskedCircleWedges Mm
        (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < η) ∧
    ∃ (D : PhysicalTerminalDisks G π (π '' Gᶜ)
        (fun s : gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ => σ s)
        (fun s => O s))
      (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      (∀ s, Disjoint (closedTerminalCap (D.H s)) (cutoffCore χ)) ∧
      cutoffCore χ ⊆ openCompletedRegion D.H ∧
      (∀ (s : gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ) l,
        active s l → ∀ δ η : ℝ,
        ∀ x ∈ frontier (jordanInterior (D.H s)),
        ∀ y ∈ frontier (jordanInterior (D.H s)),
        |shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (x : Sphere))) -
          shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (y : Sphere)))| ≤
            (b l s - a l s) + 4 * reciprocalGridStep N) ∧
      Pairwise (Disjoint on fun j => closure (jordanInterior (H j))) ∧
      (∀ s j, Disjoint (closure (jordanInterior (D.H s))) (closure (jordanInterior (H j)))) ∧
      (∀ j, Disjoint (closedTerminalCap (H j)) (cutoffCore χ)) ∧
      π ⁻¹' (π '' Gᶜ) ⊆ sphericalDiskUnion D.H ∪ sphericalDiskUnion H ∧
      cutoffCore χ ⊆ completionCore D.H H ∧ completionCore D.H H ⊆ G ∧
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
  let Pgrid (N : ℕ) (θ : Fin n → ℝ) : Prop :=
    OrderedGraphGridCompatibility R θ N (π '' Gᶜ) σ
  obtain ⟨ψ, t, K, χ, N, θ, _, _, _, _, _, hK, hK₀K, hKG, hKc, hbd,
      hχ, _, _, hχzero, hχone, hN, hPgrid, hfin, hcard, hvi, hgood⟩ :=
    exists_regular_masked_core_cutoff_and_grid hsard (isOpen_realChartDomain hG)
      (isCompact_compl_realChartDomain hG hinfty) hK₀ hK₀G Mm hMm hMmB f hf hmf hdf hf2
      Flag hFlag a b hwidth hwidth2 Pgrid
      (fun N => ae_ordered_graph_grid_compatibility R (π '' Gᶜ) σ hcompat N) hη hρ
  obtain ⟨D, m, H, γ, hD, hCQ, hosc, hHd, hDH, hHC, hcov, hCC, hCG', hcurves⟩ :=
    exists_mask_atlas_geometric_assembly hsard hsch G hG π hπ hclosed hsurj hr hTD
      (cutoffCore χ) (isCompact_cutoffCore χ) (cutoffCore_subset_domain hinfty χ hχone)
      (infty_mem_cutoffCore χ) R hR σ hσ hσB a b θ Flag hband hfin O hO U v M
      hbounded hphysical active hbudget hfree hPgrid L Mask hMask hboundary singular hflag P hP hcover
  exact ⟨K, χ, N, θ, hK, hK₀K, hKG, hKc, hbd, hχ, hχzero, hχone, hN, hfin, hcard,
    hvi, hgood, D, m, H, γ, hD, hCQ, hosc, hHd, hDH, hHC, hcov, hCC, hCG', hcurves⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
