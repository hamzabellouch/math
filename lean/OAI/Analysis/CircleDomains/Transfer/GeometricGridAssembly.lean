import OAI.Analysis.CircleDomains.Transfer.RetainedTerminalGeometry

namespace OAI

/-!
# Complete geometric assembly for a selected real-coordinate grid

The bands themselves provide the terminal oscillation budgets. After
selecting physical terminals off the core, the descending grid construction
fills the remaining dust and retains its actual one-active-coordinate
boundary condition. No disk family or containment conclusion is assumed.
-/

open Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

attribute [local instance] sphereMetric

theorem boundary_oscillation_le_of_band
    {U : Set Sphere} {f : Sphere → ℝ} {M a b : ℝ} {p : Sphere}
    (hM : ∀ x ∈ U, |f x| ≤ M) (hp : p ∈ closure U)
    (hband : {t : ℝ | (p, t) ∈ intervalFiberHull (clusterGraph U f)} = Icc a b) :
    limsup f (𝓝[U] p) - liminf f (𝓝[U] p) ≤ b - a := by
  let : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hb : ∀ᶠ x in 𝓝[U] p, -M ≤ f x ∧ f x ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact abs_le.mp (hM x hx)
  have hlo := isBoundedUnder_of_eventually_ge (hb.mono (fun _ hx => hx.1))
  have hhi := isBoundedUnder_of_eventually_le (hb.mono (fun _ hx => hx.2))
  have hle := liminf_le_limsup hhi hlo
  have heq := intervalFiberHull_clusterGraph_eq_boundary_band hM hp
  have ha : liminf f (𝓝[U] p) ∈ Icc a b := by
    rw [← hband, heq]
    exact ⟨le_rfl, hle⟩
  have hb' : limsup f (𝓝[U] p) ∈ Icc a b := by
    rw [← hband, heq]
    exact ⟨hle, le_rfl⟩
  linarith [ha.1, hb'.2]

theorem exists_geometric_grid_assembly
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (hG : IsOpen G) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    (C : Set Sphere) (hC : IsCompact C) (hCG : C ⊆ G) (hinfty : OnePoint.infty ∈ C)
    {n N : ℕ} {S : Type*}
    (U : Set Sphere) (f : Fin n → Sphere → ℝ) (M : Fin n → ℝ)
    (hbounded : ∀ l x, x ∈ U → |f l x| ≤ M l)
    (hphysical : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (hσU : ∀ s, σ s ∈ closure U)
    (a b : Fin n → S → ℝ) (θ : Fin n → ℝ) (F : Set S)
    (hband : ∀ l s, {t : ℝ | (σ s, t) ∈ intervalFiberHull (clusterGraph U (f l))} =
      Icc (a l s) (b l s))
    (hfin : (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite)
    (O : (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) → Set Sphere)
    (hO : ∀ s : gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ,
      O s ∈ 𝓝 (σ s))
    (hfree : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l,
      ∃ v : ℝ, {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U (f l))} = {v})
    (hcompat : OrderedBandGridCompatibility U f θ N (π '' Gᶜ) σ) :
    ∃ (D : PhysicalTerminalDisks G π (π '' Gᶜ)
        (fun s : gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ => σ s) O)
      (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      (∀ s, Disjoint (closedTerminalCap (D.H s)) C) ∧
      C ⊆ openCompletedRegion D.H ∧
      (∀ s l, ∀ δ η : ℝ, ∀ x ∈ frontier (jordanInterior (D.H s)),
        ∀ y ∈ frontier (jordanInterior (D.H s)),
        |shiftedStaircase (reciprocalGridStep N) δ η (f l (π (x : Sphere))) -
          shiftedStaircase (reciprocalGridStep N) δ η (f l (π (y : Sphere)))| ≤
            (b l s - a l s) + 4 * reciprocalGridStep N) ∧
      Pairwise (Disjoint on fun j => closure (jordanInterior (H j))) ∧
      (∀ s j, Disjoint (closure (jordanInterior (D.H s))) (closure (jordanInterior (H j)))) ∧
      (∀ j, Disjoint (closedTerminalCap (H j)) C) ∧
      π ⁻¹' (π '' Gᶜ) ⊆ sphericalDiskUnion D.H ∪ sphericalDiskUnion H ∧
      C ⊆ completionCore D.H H ∧ completionCore D.H H ⊆ G ∧
      (∀ j, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ j) ∧ Topology.IsEmbedding (γ j) ∧
        frontier (jordanInterior (H j)) = range (γ j) ∧
        (∀ z ∈ frontier (jordanInterior (H j)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ π '' Gᶜ) ∧
        ∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
          Disjoint (frontier (jordanInterior (H j)))
            ((fun z : ℂ => π (z : Sphere)) ⁻¹' (⋃ r, reciprocalBandLevel U (f l) (θ l) N r))) := by
  let : Fintype (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ) := hfin.fintype
  obtain ⟨D, hD, hCQ, hosc⟩ := exists_retained_physical_terminals_with_staircase_bound
    hsard hsch hG hC hCG hinfty π hπ hclosed hsurj hr hTD
    (fun s : gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ => σ s)
    (hσ.comp Subtype.val_injective) (fun s => hσB s) O hO
    (fun _ => U) (fun _ l => f l) (fun _ l => M l) (fun _ => hbounded)
    (fun _ z hz _ => hphysical z hz) (fun _ _ => True) (fun s l => b l s - a l s)
    (fun s l _ => boundary_oscillation_le_of_band (hbounded l) (hσU s) (hband l s))
    (reciprocalGridStep_pos N)
  obtain ⟨m, H, γ, hHd, hDH, hHC, hcover, hCC, hCG', hcurves⟩ :=
    exists_geometric_completion_for_grid hsard hsch G π hπ hclosed hsurj hr
      (hG.isClosed_compl.isCompact.image hπ).isClosed rfl hTD hC hCG hinfty
      U f M hbounded σ hσB a b θ F hband hfin O D hD
      (fun x hx => hfree x hx.1) (fun x hx => hcompat x hx.1)
  exact ⟨D, m, H, γ, hD, hCQ, fun s l => hosc s l trivial,
    hHd, hDH, hHC, hcover, hCC, hCG', hcurves⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
