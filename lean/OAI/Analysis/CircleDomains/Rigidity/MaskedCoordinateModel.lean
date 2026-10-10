import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateData
import OAI.Analysis.CircleDomains.Transfer.MarkedModelTerminalControl

namespace OAI

/-! Assemble a finite family of actual coordinates. The common marked
branches and all terminal estimates are constructed from their retained
atlas data and band endpoints. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_model_of_masked_coordinates
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    {G U : Set Sphere} (hG : IsOpen G) (hinfty : OnePoint.infty ∈ G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ)) (hUB : U ⊆ (π '' Gᶜ)ᶜ)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {n : ℕ} (hn : 0 < n) {S : Type*} [Countable S]
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (hσU : ∀ s, σ s ∉ U) (C : Fin n → MaskedCoordinateData G U π σ)
    (Flag : Set S) (hFlag : Flag.Finite) (hflag : ∀ l, (C l).singular ∈ Flag)
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (C j).graph (fun l => (C l).graph) labels) = 0)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (k₀ : ℕ) :
    ∃ (K : Set (ℝ × ℝ)) (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ),
      let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair
        (fun l => (C l).lower) (fun l => (C l).upper) θ
      A.Finite ∧ ∃ (D : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => σ s) (fun s => O s))
        (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ)
        (Q : MaskedModelData D.H H (realChartDomain G) K
          (fun l => physicalMask π (C l).mask) (fun l => (C l).physical) χ N θ ε),
        k₀ ≤ Q.widthIndex ∧ IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ realChartDomain G ∧
        IsCompact (closure Kᶜ) ∧ sphericalCore K ⊆ openCompletedRegion D.H ∧
        reciprocalGridStep N < ρ ∧
        ∃ (E : A → Set (ℝ × ℝ)) (w : A → Fin n → (ℝ × ℝ) → ℝ),
          (∀ s, IsOpen (E s) ∧ frontier (realJordanInterior (D.H s)) ⊆ E s) ∧
          (∀ l (s : A), σ s ∈ (C l).mask → σ s ≠ σ (C l).singular →
            ContDiffOn ℝ ∞ (w s l) (E s) ∧
              ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (D.H s))),
                (w s l x : UnitAddCircle) = Q.functions l x) ∧
          ∀ l, Real.sqrt (∑' s : {s : A // σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular},
            max (Metric.diam (w s l '' frontier (realJordanInterior (D.H s))) -
              ((C l).upper s - (C l).lower s)) 0 ^ 2) < ε := by
  obtain ⟨V, u, B, hV, hVM, _, hub, hwidth, hus, hup⟩ :=
    exists_marked_physical_branches (fun l => (C l).Index) U G π
      (fun l => (C l).mask) (fun l => (C l).mask_closed) (fun l => (C l).mask_frontier)
      σ hσU (fun l => σ (C l).singular) (fun l => (C l).patch) (fun l => (C l).patch_open)
      (fun l => (C l).branch) (fun l => (C l).bound) (fun l => (C l).branch_bounded)
      (fun l => (C l).lower) (fun l => (C l).upper) (fun s l => (C l).marked_branch s)
      (fun l => (C l).physical) (fun l => (C l).branch_smooth) (fun l => (C l).branch_projection)
  let O' (s : S) := O s ∩ V s
  have hO' (s : S) : O' s ∈ 𝓝 (σ s) := inter_mem (hO s) ((hV s).1.mem_nhds (hV s).2)
  let active (s : S) (l : Fin n) := σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular
  obtain ⟨K, χ, N, θ, hA, D, m, H, Q, hk, hK, hK₀K, hKG, hKc, hKQ,
      _, _, _, hTC, hTH, hN, hcard, hosc⟩ :=
    exists_assembled_masked_model hsard hsch hcompact hfinite G hG hinfty
      π hπ hclosed hsurj hr hTD hK₀ hK₀G hn (fun l => (C l).graph)
      (fun l => (C l).graph_closed) σ hσ hσB (fun l => (C l).lower)
      (fun l => (C l).upper) Flag hFlag (fun l => (C l).width_nonneg)
      (fun l => (C l).width_summable) (fun l => (C l).marked_fiber)
      (fun l => (C l).Index) (fun l => (C l).mask) (fun l => (C l).mask_closed)
      (fun l => ((C l).mask_frontier).trans hUB) (fun l => (C l).singular) hflag
      (fun l => (C l).patch) (fun l => (C l).patch_open) (fun l => (C l).cover)
      (fun l => (C l).physical) (fun l => (C l).smooth) (fun l => (C l).measurable)
      (fun l => (C l).gradient_measurable) (fun l => (C l).energy)
      (fun l i x => (C l).branch i (π (Complex.equivRealProdCLM.symm x : Sphere)))
      (fun l => (C l).branch_smooth) (fun l => (C l).branch_projection)
      (fun l => (C l).physical_graph) O' hO' (fun s => U ∩ V s) u B
      (fun s l x _ => hub s l x)
      (fun s z hzG hz => ⟨hPU z hzG, hz.2⟩) active
      (fun s l hs => (hwidth s l hs.1 hs.2).le)
      (fun x hx hfree l => (C l).free_fiber x hx hfree) hcompat hε hρ k₀
  let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair
    (fun l => (C l).lower) (fun l => (C l).upper) θ
  let : Fintype A := hA.fintype
  let selected (l : Fin n) : Finset A := Finset.univ.filter (fun s => active s l)
  obtain ⟨E, w, hE, hw, hexcess⟩ := marked_model_terminal_control hG hπ D H hTH
    (fun l => (C l).mask) Q hTC (fun s => V s) (fun s => (hV s).1)
    (fun s => inter_subset_right) (fun s => u s) selected
    (fun s l => (C l).upper s - (C l).lower s)
    (fun l s hs => (hVM s l (Finset.mem_filter.mp hs).2.1).trans interior_subset)
    (fun l s hs => hus s l (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp hs).2.2)
    (fun l s hs => hup s l (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp hs).2.2)
    (fun l s _ => (C l).width_nonneg s)
    (fun l s hs => hosc s l (Finset.mem_filter.mp hs).2 _ _)
    (by simpa only [A, Set.fintypeCard_eq_ncard] using hcard)
  let D' : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => σ s) (fun s => O s) :=
    { D with closure_subset := fun s z hz => (D.closure_subset s hz).1 }
  refine ⟨K, χ, N, θ, hA, D', m, H, Q, hk, hK, hK₀K, hKG, hKc, hKQ, hN,
    E, w, hE, ?_, ?_⟩
  · intro l s hs hn
    exact hw l s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hn⟩)
  · intro l
    have he : (∑' s : {s : A // σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular},
        max (Metric.diam (w s l '' frontier (realJordanInterior (D.H s))) -
          ((C l).upper s - (C l).lower s)) 0 ^ 2) =
        ∑ s ∈ selected l, max (Metric.diam (w s l '' frontier (realJordanInterior (D.H s))) -
          ((C l).upper s - (C l).lower s)) 0 ^ 2 := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype
        (p := fun s : A => σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular) (selected l)
        (by intro s; simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and, active])
        (fun s => max (Metric.diam (w s l '' frontier (realJordanInterior (D.H s))) -
          ((C l).upper s - (C l).lower s)) 0 ^ 2)).symm
    rw [he]
    exact (hexcess l).trans (by linarith)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
