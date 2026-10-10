import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Selection.MixedCoordinateStage
import OAI.Analysis.CircleDomains.Selection.RealCoordinateSubfamily
import OAI.Analysis.CircleDomains.Transfer.AssembledMixedModel
import OAI.Analysis.CircleDomains.Transfer.ModelRealTerminals
import OAI.Analysis.CircleDomains.Selection.SubfamilyOverride

namespace OAI

/-! Construct the actual common model for both real barriers and masked
periods. Real terminal bounds include every mark. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem nonempty_mixed_coordinate_stage
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
    {m : ℕ} (ι : Fin m → Fin n) (hι : Injective ι) (R : RealCoordinateSubfamily C ι)
    (Flag : Set S) (hFlag : Flag.Finite) (hflag : ∀ l, (C l).singular ∈ Flag)
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (C j).graph (fun l => (C l).graph) labels) = 0)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (k₀ : ℕ) :
    Nonempty (MixedCoordinateStage C ι R.physical Flag O K₀ ε ρ k₀) := by
  classical
  obtain ⟨V, u, B, hV, hVM, _, hub, hwidth, hus, hup⟩ :=
    exists_marked_physical_branches (fun l => (C l).Index) U G π
      (fun l => (C l).mask) (fun l => (C l).mask_closed) (fun l => (C l).mask_frontier)
      σ hσU (fun l => σ (C l).singular) (fun l => (C l).patch) (fun l => (C l).patch_open)
      (fun l => (C l).branch) (fun l => (C l).bound) (fun l => (C l).branch_bounded)
      (fun l => (C l).lower) (fun l => (C l).upper) (fun s l => (C l).marked_branch s)
      (fun l => (C l).physical) (fun l => (C l).branch_smooth) (fun l => (C l).branch_projection)
  let v (s : S) := subfamilyOverride ι R.quotient (u s)
  let B' (s : S) := subfamilyOverride ι R.bound (B s)
  have hvreal (s : S) (j : Fin m) : v s (ι j) = R.quotient j :=
    subfamilyOverride_at ι hι R.quotient (u s) j
  have hvother (s : S) {l : Fin n} (hl : l ∉ range ι) : v s l = u s l :=
    subfamilyOverride_of_notMem ι R.quotient (u s) hl
  have hvbound (s : S) (l : Fin n) (x : Sphere) (hx : x ∈ U ∩ V s) :
      |v s l x| ≤ B' s l := by
    by_cases hl : l ∈ range ι
    · obtain ⟨j, rfl⟩ := hl
      rw [hvreal, show B' s (ι j) = R.bound j from subfamilyOverride_at ι hι _ _ j]
      exact R.bounded j x hx.1
    · rw [hvother s hl, show B' s l = B s l from subfamilyOverride_of_notMem ι _ _ hl]
      exact hub s l x
  let O' (s : S) := O s ∩ V s
  have hO' (s : S) : O' s ∈ 𝓝 (σ s) := inter_mem (hO s) ((hV s).1.mem_nhds (hV s).2)
  let active (s : S) (l : Fin n) := l ∈ range ι ∨
    (σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular)
  have hvwidth (s : S) (l : Fin n) (hl : active s l) :
      limsup (v s l) (𝓝[U ∩ V s] (σ s)) -
        liminf (v s l) (𝓝[U ∩ V s] (σ s)) ≤ (C l).upper s - (C l).lower s := by
    by_cases hi : l ∈ range ι
    · obtain ⟨j, rfl⟩ := hi
      rw [hvreal, nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds ((hV s).1.mem_nhds (hV s).2))]
      exact R.width j s
    · rw [hvother s hi]
      exact (hwidth s l (hl.resolve_left hi).1 (hl.resolve_left hi).2).le
  have hvsmooth (s : S) (l : Fin n) (hs : σ s ∈ (C l).mask)
      (hne : σ s ≠ σ (C l).singular) : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => v s l (π (Complex.equivRealProdCLM.symm x : Sphere)))
      (realChartDomain G ∩ realChartDomain (π ⁻¹' V s)) := by
    by_cases hi : l ∈ range ι
    · obtain ⟨j, rfl⟩ := hi
      rw [hvreal]
      exact ((R.smooth j).mono inter_subset_left).congr
        (fun x hx => R.pullback j x hx.1)
    · rw [hvother s hi]
      exact hus s l hs hne
  have hvproj (s : S) (l : Fin n) (hs : σ s ∈ (C l).mask)
      (hne : σ s ≠ σ (C l).singular) (x : ℝ × ℝ)
      (hx : x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' V s)) :
      (v s l (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = (C l).physical x := by
    by_cases hi : l ∈ range ι
    · obtain ⟨j, rfl⟩ := hi
      rw [hvreal, R.pullback j x hx.1]
      exact R.projection j x
    · rw [hvother s hi]
      exact hup s l hs hne x hx
  obtain ⟨K, χ, N, θ, hA, D, k, H, Q, W, hk, hK, hK₀K, hKG, hKc, hKQ,
      _, _, _, hTC, hTH, hN, hcard, hosc⟩ :=
    exists_assembled_mixed_model hsard hsch hcompact hfinite G hG hinfty
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
      (fun l => (C l).physical_graph) ι hι R.physical R.smooth R.full_mask R.projection
      O' hO' (fun s => U ∩ V s) v B' hvbound
      (fun s z hzG hz => ⟨hPU z hzG, hz.2⟩) active hvwidth
      (fun x hx hfree l => (C l).free_fiber x hx hfree) hcompat hε hρ k₀
  let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair
    (fun l => (C l).lower) (fun l => (C l).upper) θ
  let : Fintype A := hA.fintype
  let selected (l : Fin n) : Finset A := Finset.univ.filter
    (fun s => σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular)
  obtain ⟨E, w, hE, hw, hexcess⟩ := marked_model_terminal_control hG hπ D H hTH
    (fun l => (C l).mask) Q hTC (fun s => V s) (fun s => (hV s).1)
    (fun s => inter_subset_right) (fun s => v s) selected
    (fun s l => (C l).upper s - (C l).lower s)
    (fun l s hs => (hVM s l (Finset.mem_filter.mp hs).2.1).trans interior_subset)
    (fun l s hs => hvsmooth s l (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp hs).2.2)
    (fun l s hs => hvproj s l (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp hs).2.2)
    (fun l s _ => (C l).width_nonneg s)
    (fun l s hs => hosc s l (Or.inr (Finset.mem_filter.mp hs).2) _ _)
    (by simpa only [A, Set.fintypeCard_eq_ncard] using hcard)
  have hrealosc := W.terminal_oscillation hTH hTC
    (fun (s : A) j => (C (ι j)).upper s - (C (ι j)).lower s)
    (fun s j => (C (ι j)).width_nonneg s) (fun s j x hx y hy => by
      have h := hosc s (ι j) (Or.inl (mem_range_self j))
        (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j)) x hx y hy
      rw [hvreal] at h
      have hp (z : ℂ) (hz : z ∈ frontier (jordanInterior (D.H s))) :
          R.quotient j (π (z : Sphere)) = R.physical j (Complex.equivRealProdCLM z) := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using
          R.pullback j (Complex.equivRealProdCLM z) (by
            simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using
              (D.frontier_good s z hz).1)
      simpa only [hp x hx, hp y hy] using h)
  let D' : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => σ s) (fun s => O s) :=
    { D with closure_subset := fun s z hz => (D.closure_subset s hz).1 }
  refine ⟨{
    indices := A
    indices_finite := hA
    flags := fun _ hs => Or.inl hs
    terminals := D'
    fillCount := k
    filling := H
    core := K
    core_closed := hK
    core_contains := hK₀K
    core_source := hKG
    core_cocompact := hKc
    core_model := hKQ
    cutoff := χ
    grid := N
    offset := θ
    small_grid := hN
    model := Q
    late_width := hk
    terminal_domain := E
    terminal_branch := w
    terminal_open := fun s => (hE s).1
    terminal_frontier := fun s => (hE s).2
    terminal_lift := ?_
    terminal_excess := ?_
    real := W
    real_excess := ?_ }⟩
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
        (by intro s; simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and])
        (fun s => max (Metric.diam (w s l '' frontier (realJordanInterior (D.H s))) -
          ((C l).upper s - (C l).lower s)) 0 ^ 2)).symm
    rw [he]
    exact (hexcess l).trans (by linarith)
  · intro j
    rw [tsum_fintype]
    have h := sqrt_sum_terminal_excess_sq_lt Finset.univ Finset.univ (Subset.refl _)
      (fun s : A => terminalOscillation (D.H s) (W.functions j))
      (fun s : A => (C (ι j)).upper s - (C (ι j)).lower s) (reciprocalGridStep_pos N).le
      (fun s _ => hrealosc s j)
      (by simpa only [Finset.card_univ, A, Set.fintypeCard_eq_ncard] using hcard)
    exact h.trans (by linarith)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
