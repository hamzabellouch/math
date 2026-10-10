import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.GeometricGridAssembly
import OAI.Analysis.CircleDomains.Rigidity.PrincipalRealTransfer
import OAI.Analysis.CircleDomains.Transfer.TerminalTransfer
import OAI.Analysis.CircleDomains.Modulus.FiniteBandNorm
import OAI.Analysis.CircleDomains.Transfer.OrderedGridCompatibility

namespace OAI

/-!
# Real finite transfer from the original coordinate data

The regular core, reciprocal grid, physical terminal disks, remaining
fillings, common metric and principal circle model are selected together.
Both the localized energy inequality and the physical terminal excess
refer to these same choices.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_assembled_real_transfer
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {G : Set Sphere} (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {n : ℕ} (hn : 0 < n) (u : Fin n → (ℝ × ℝ) → ℝ)
    (huM : ∀ l, Measurable (u l))
    (hu : ∀ l, ContDiffOn ℝ ∞ (u l) (realChartDomain G))
    (hu2 : ∀ l, MemLp (planarGradient (u l)) 2 (volume.restrict (realChartDomain G)))
    {S : Type*} [Countable S] (σ : S → Sphere) (hσ : Injective σ)
    (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (U : Set Sphere) (hU : IsOpen U) (f : Fin n → Sphere → ℝ)
    (hf : ∀ l, ContinuousOn (f l) U) (M : Fin n → ℝ)
    (hbounded : ∀ l x, x ∈ U → |f l x| ≤ M l)
    (hphysical : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (hpull : ∀ l (z : ℂ), (z : Sphere) ∈ G → u l (Complex.equivRealProdCLM z) = f l (π z))
    (hσU : ∀ s, σ s ∈ closure U)
    (a b : Fin n → S → ℝ) (hwidth : ∀ l s, 0 ≤ b l s - a l s)
    (hwidth2 : ∀ l, Summable (fun s => (b l s - a l s) ^ 2))
    (hband : ∀ l s, {t : ℝ | (σ s, t) ∈ intervalFiberHull (clusterGraph U (f l))} =
      Icc (a l s) (b l s))
    (Flag : Set S) (hFlag : Flag.Finite)
    (hfree : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l,
      ∃ v : ℝ, {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U (f l))} = {v})
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (circleBandGraph U (f j))
          (fun i => circleBandGraph U (f i)) labels) = 0)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (k₀ : ℕ) :
    ∃ (N : ℕ) (θ : Fin n → ℝ),
      let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ
      A.Finite ∧ ∃ (K : Set (ℝ × ℝ)) (χ : (ℝ × ℝ) → ℝ)
        (D : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => σ s) (fun s => O s))
        (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (k : ℕ) (F : Fin n → (ℝ × ℝ) → ℝ)
        (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric)
        (V : Set Sphere) (φ φi : Sphere → Sphere),
        reciprocalGridStep N < ρ ∧ k₀ ≤ k ∧ IsClosed K ∧ K₀ ⊆ interior K ∧
        K ⊆ realChartDomain G ∧ IsCompact (closure Kᶜ) ∧
        sphericalCore K ⊆ openCompletedRegion D.H ∧
        IsFilledCoordinateFamily (fun j => realJordanInterior (H j))
          (realChartDomain G ∪ ⋃ j, realJordanInterior (H j))
          (cutoffCoordinateFamily u χ (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
        (∀ᶠ z in 𝓝ˢ K, ∀ l, F l z = u l z) ∧
        0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
        (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
        (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
        (∀ l (E : Set (ℝ × ℝ)), MeasurableSet E → E ⊆ K →
          (∫ z in realChartDomain (completedRegion D.H) \ E, gradientEnergy (F l) g z) <
            (∫ z in realChartDomain G \ E,
              gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) z) + ε) ∧
        (∀ l, Real.sqrt (∑' s : A,
          max (terminalOscillation (D.H s) (F l) - (b l s - a l s)) 0 ^ 2) < ε) ∧
        (∀ l, Real.sqrt (∑' s : A, terminalOscillation (D.H s) (F l) ^ 2) <
          Real.sqrt (∑' s : S, (b l s - a l s) ^ 2) + ε) ∧
        IsCircleDomain V ∧ IsSmoothSphereEquivalence φ φi (openCompletedRegion D.H) V ∧
        IsConformalOn φ (sphericalCore K) ∧ IsPrincipalNormalized φ ∧
        (∀ p ∈ openCompletedRegion D.H, IsMetricConformalAt g φ p) ∧
        (∀ l, IntegrableOn (gradientEnergy (F l) g) (realChartDomain (completedRegion D.H))) ∧
        (∀ l, ContDiffOn ℝ ∞ (F l ∘ sphereRealMap φi) (realChartDomain V)) ∧
        realChartDomain (completedRegion D.H) ⊆ realChartDomain G ∪ ⋃ j, realJordanInterior (H j) := by
  classical
  let P (N : ℕ) (θ : Fin n → ℝ) : Prop :=
    OrderedBandGridCompatibility U f θ N (π '' Gᶜ) σ
  obtain ⟨K, ψ, χ, t, N, θ, _, _, _, _, _, hK, hK₀K, hKG, hKc,
      hχ, _, _, hχzero, hχone, hN, hP, hfin, hcard, hvi, hgood⟩ :=
    exists_regular_core_cutoff_and_grid hsard (isOpen_realChartDomain hG)
      (isCompact_compl_realChartDomain hG hinf) hK₀ hK₀G u huM hu hu2
      Flag hFlag a b hwidth hwidth2 P
      (fun N => ae_ordered_band_grid_compatibility U f (π '' Gᶜ) σ hcompat N)
      (div_pos hε (by norm_num : (0 : ℝ) < 8)) hρ
  let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ
  let : Fintype A := hfin.fintype
  have hCsub := cutoffCore_subset_domain hinf χ hχone
  obtain ⟨D, m, H, _, hDavoid, hCQ, hDosc, hHd, hDH, hHC, hcover, _, _, hcurves⟩ :=
    exists_geometric_grid_assembly hsard hsch G hG π hπ hclosed hsurj hr hTD
      (cutoffCore χ) (isCompact_cutoffCore χ) hCsub (infty_mem_cutoffCore χ)
      U f M hbounded hphysical σ hσ hσB hσU a b θ Flag hband hfin
      (fun s => O s) (fun s => hO s) hfree hP
  have hKQ : sphericalCore K ⊆ openCompletedRegion D.H :=
    (sphericalCore_subset_cutoffCore χ hχzero).trans hCQ
  have hbad : ∀ x ∈ Gᶜ, π x ∈ π '' Gᶜ := fun x hx => mem_image_of_mem _ hx
  have hgood' : ∃ᶠ k in atTop, (∫ z in realChartDomain G \ K,
      coordinateWedges (natCoordinateFamily (cutoffCoordinateFamily u χ (reciprocalGridStep N)
        (staircaseWidth (reciprocalGridStep N) k) θ)) n z) < ε / 2 :=
    hgood.mono (fun _ hk => hk.trans (by linarith))
  obtain ⟨k, F, R, g, V, φ, φi, hk, hF, hretain, hR, hg, hPD, hcore, hfar,
      _, hlocal, hV, heq, hconf, hnorm, hsmooth, _, hmetric, hint⟩ :=
    principal_real_coordinate_transfer_from_grid hcompact hfinite hn D.H H D.disjoint_closures hHd
      hG π hbad hcover hK hKc hKG hKQ u hu hu2 χ hχ hχzero hHC
      (fun j z hz => ((hcurves j).2.2.2.1 z hz).1)
      U hU f hf (fun z : ℂ => π z)
      (fun j z hz => hphysical z ((hcurves j).2.2.2.1 z hz).1)
      (fun j l z hz => congrArg (fun r : ℝ => (r : UnitAddCircle))
        (hpull l z ((hcurves j).2.2.2.1 z hz).1))
      θ (fun j => (hcurves j).2.2.2.2) hvi hgood' k₀
  have hosc : ∀ l, Real.sqrt (∑ s : A,
      max (terminalOscillation (D.H s) (F l) - (b l s - a l s)) 0 ^ 2) < ε := by
    have hs := transferred_terminal_oscillation_bound (η := ε / 8) D.H H hDH u χ
      (reciprocalGridStep_pos N).le θ hF hDavoid (fun s l => b l s - a l s)
      (fun s l => hwidth l s) ?_ ?_
    · intro l
      exact (hs l).trans (by linarith)
    · intro s l x hx y hy
      rw [hpull l x (D.frontier_good s x hx).1, hpull l y (D.frontier_good s y hy).1]
      exact hDosc s l _ _ x hx y hy
    · simpa only [A, Set.fintypeCard_eq_ncard] using hcard
  refine ⟨N, θ, hfin, K, χ, D, m, H, k, F, R, g, V, φ, φi,
    hN, hk, hK, hK₀K, hKG, hKc, hKQ, hF, hretain, hR, hg, hPD, hcore, hfar,
    ?_, ?_, ?_, hV, heq, hconf, hnorm, hmetric, hint, (fun l => (hsmooth l).1),
    real_completedRegion_subset_extension D.H H G (π '' Gᶜ) π hbad hcover⟩
  · intro l E hE hEK
    simpa only [natCoordinateFamily, dite_eq_left l.isLt] using hlocal l.val l.isLt E hE hEK
  · intro l
    simpa only [tsum_fintype] using hosc l
  · intro l
    rw [tsum_fintype]
    exact (CircleDomainRigidity.sqrt_sum_sq_le_band_add_excess
      (fun s : A => terminalOscillation (D.H s) (F l)) (fun s : A => b l s - a l s)
      (fun _ => Metric.diam_nonneg) (fun s => hwidth l s)).trans_lt
      (add_lt_add_of_le_of_lt (CircleDomainRigidity.finite_label_band_norm_le
        (fun s : A => (s : S)) Subtype.val_injective (fun s => b l s - a l s) (hwidth2 l))
        (hosc l))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
