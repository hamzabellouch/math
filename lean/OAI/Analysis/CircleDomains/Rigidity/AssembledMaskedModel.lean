import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.PreparedMaskAtlasGeometry
import OAI.Analysis.CircleDomains.Rigidity.RealCapMaskNeighborhoods
import OAI.Analysis.CircleDomains.Rigidity.MaskedModelData

namespace OAI

/-! One actual grid, all terminal and filling caps, the common metric,
and the principal finite model are constructed from the original masked
coordinates. The boundary graphs are used only through their proved
compatibility and the local real branches. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 def physicalMask (π : Sphere → Sphere) (M : Set Sphere) : Set (ℝ × ℝ) :=
  realChartDomain (π ⁻¹' M)

 theorem exists_assembled_masked_model
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (G : Set Sphere) (hG : IsOpen G) (hinfty : OnePoint.infty ∈ G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {n : ℕ} (hn : 0 < n) {S : Type*} [Countable S]
    (R : Fin n → Set (Sphere × UnitAddCircle)) (hR : ∀ l, IsClosed (R l))
    (σ : S → Sphere) (hσ : Injective σ) (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (a b : Fin n → S → ℝ) (Flag : Set S) (hFlag : Flag.Finite)
    (hwidth : ∀ l s, 0 ≤ b l s - a l s)
    (hwidth2 : ∀ l, Summable (fun s => (b l s - a l s) ^ 2))
    (hband : ∀ l s, {t : UnitAddCircle | (σ s, t) ∈ R l} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (a l s) (b l s))
    (L : Fin n → Type*) (Mask : Fin n → Set Sphere) (hMask : ∀ l, IsClosed (Mask l))
    (hboundary : ∀ l, frontier (Mask l) ⊆ (π '' Gᶜ)ᶜ)
    (singular : Fin n → S) (hflag : ∀ l, singular l ∈ Flag)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (hcover : ∀ l, Mask l \ {σ (singular l)} ⊆ ⋃ i, P l i)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (realChartDomain G ∩ interior (physicalMask π (Mask l))))
    (hmf : ∀ l, Measurable (f l)) (hdf : ∀ l, Measurable (circleGradient (f l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2
      ((volume.restrict (realChartDomain G)).restrict (physicalMask π (Mask l))))
    (vp : ∀ l, L l → (ℝ × ℝ) → ℝ)
    (hvp : ∀ l i, ContDiffOn ℝ ∞ (vp l i)
      (realChartDomain G ∩ realChartDomain (π ⁻¹' P l i)))
    (hproj : ∀ l i x, x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' P l i) →
      (vp l i x : UnitAddCircle) = f l x)
    (hgraph : ∀ l x, x ∈ realChartDomain G ∩ interior (physicalMask π (Mask l)) →
      (π (Complex.equivRealProdCLM.symm x : Sphere), f l x) ∈ R l)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    (U : S → Set Sphere) (v : S → Fin n → Sphere → ℝ) (B : S → Fin n → ℝ)
    (hbounded : ∀ s l x, x ∈ U s → |v s l x| ≤ B s l)
    (hphysical : ∀ s (z : ℂ), (z : Sphere) ∈ G → π (z : Sphere) ∈ O s → π (z : Sphere) ∈ U s)
    (active : S → Fin n → Prop)
    (hbudget : ∀ s l, active s l →
      limsup (v s l) (𝓝[U s] (σ s)) - liminf (v s l) (𝓝[U s] (σ s)) ≤ b l s - a l s)
    (hfree : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l, {t : UnitAddCircle | (x, t) ∈ R l}.Subsingleton)
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (R j) R labels) = 0)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (k₀ : ℕ) :
    ∃ (K : Set (ℝ × ℝ)) (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ),
      let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ
      A.Finite ∧ ∃ (D : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => σ s) (fun s => O s))
        (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ)
        (Q : MaskedModelData D.H H (realChartDomain G) K
          (fun l => physicalMask π (Mask l)) f χ N θ ε),
        k₀ ≤ Q.widthIndex ∧ IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ realChartDomain G ∧
        IsCompact (closure Kᶜ) ∧ sphericalCore K ⊆ openCompletedRegion D.H ∧
        (∀ l, frontier (physicalMask π (Mask l)) ⊆ interior K) ∧
        ContDiff ℝ ∞ χ ∧ (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧
        (∀ s, Disjoint (closedTerminalCap (D.H s)) (cutoffCore χ)) ∧
        (∀ s j, Disjoint (closure (jordanInterior (D.H s))) (closure (jordanInterior (H j)))) ∧
        reciprocalGridStep N < ρ ∧ reciprocalGridStep N * Real.sqrt (A.ncard : ℝ) < ε / 8 ∧
        ∀ (s : A) l, active s l → ∀ δ η : ℝ,
          ∀ x ∈ frontier (jordanInterior (D.H s)), ∀ y ∈ frontier (jordanInterior (D.H s)),
          |shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (x : Sphere))) -
            shiftedStaircase (reciprocalGridStep N) δ η (v s l (π (y : Sphere)))| ≤
              b l s - a l s + 4 * reciprocalGridStep N := by
  classical
  let q : ℂ → Sphere := fun z => π (z : Sphere)
  let qr : (ℝ × ℝ) → Sphere := q ∘ Complex.equivRealProdCLM.symm
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hqr : Continuous qr := hq.comp Complex.equivRealProdCLM.symm.continuous
  let Mm : Fin n → Set (ℝ × ℝ) := fun l => physicalMask π (Mask l)
  have hMm (l : Fin n) : IsClosed (Mm l) := (hMask l).preimage hqr
  have hMmB (l : Fin n) : frontier (Mm l) ⊆ realChartDomain G := by
    intro x hx
    have hm := hqr.frontier_preimage_subset (Mask l) hx
    have hn := hboundary l hm
    change (Complex.equivRealProdCLM.symm x : Sphere) ∈ G
    by_contra hg
    exact hn ⟨(Complex.equivRealProdCLM.symm x : Sphere), hg, rfl⟩
  obtain ⟨K, χ, N, θ, hK, hK₀K, hKG, hKc, hbd, hχ, hχzero, hχone, hN, hfin, hcard,
      hvi, hgood, D, m, H, γ, hD, hCQ, hosc, hHd, hDH, hHC, hcov, _, _, hcurves⟩ :=
    exists_prepared_mask_atlas_geometry hsard hsch G hG π hπ hclosed hsurj hr hTD
      hinfty hK₀ hK₀G R hR σ hσ hσB a b Flag hFlag hwidth hwidth2 hband
      Mm (fun l => (hMm l).measurableSet) hMmB f hf hmf hdf hf2
      O hO U v B hbounded hphysical active hbudget hfree hcompat L Mask hMask hboundary
      singular hflag P hP hcover (div_pos hε (by norm_num : (0 : ℝ) < 8)) hρ
  let A := gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ
  let : Fintype A := hfin.fintype
  have hKQ : sphericalCore K ⊆ openCompletedRegion D.H :=
    (sphericalCore_subset_cutoffCore χ hχzero).trans hCQ
  have hbad : ∀ x ∈ Gᶜ, π x ∈ π '' Gᶜ := fun x hx => mem_image_of_mem π hx
  obtain ⟨Nbh, hNbh, hbranches⟩ := exists_real_cap_mask_neighborhoods H q hq L Mask hMask P hP
    (fun j => (hcurves j).2.2.2.2.2)
  have hbg := real_boundary_in_domain_and_plateau H χ
    (fun j z hz => ((hcurves j).2.2.2.1 z hz).1) hHC
  have hBG (j : Fin m) : frontier (realJordanInterior (H j)) ⊆ realChartDomain G := by
    rw [frontier_realJordanInterior]
    rintro x ⟨z, hz, rfl⟩
    exact (hbg j z hz).1
  have hBχ (j : Fin m) : frontier (realJordanInterior (H j)) ⊆ interior {x | χ x = 1} := by
    rw [frontier_realJordanInterior]
    rintro x ⟨z, hz, rfl⟩
    exact (hbg j z hz).2
  have hBK (j : Fin m) : Disjoint (frontier (realJordanInterior (H j))) K := by
    apply Set.disjoint_left.mpr
    intro x hx hk
    have h1 : χ x = 1 := (show x ∈ {x | χ x = 1} from interior_subset (hBχ j hx))
    have h0 := hχzero.self_of_nhdsSet x hk
    linarith
  have hgrid (j : Fin m) : ∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
      Disjoint (frontier (realJordanInterior (H j)))
        (qr ⁻¹' (⋃ r, reciprocalGraphLevel (R l) (θ l) N r)) := by
    obtain ⟨k, hk⟩ := (hcurves j).2.2.2.2.1
    refine ⟨k, fun l hl => ?_⟩
    apply Set.disjoint_left.mpr
    intro x hx hm
    rw [frontier_realJordanInterior] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact Set.disjoint_left.mp (hk l hl) hz (by
      simpa only [qr, q, Function.comp_apply, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hm)
  have h2 (l : Fin n) : MemLp (circleGradient (f l)) 2 (volume.restrict (realChartDomain G ∩ Mm l)) := by
    have hh := hf2 l
    change MemLp (circleGradient (f l)) 2 ((volume.restrict (realChartDomain G)).restrict (Mm l)) at hh
    simpa only [Measure.restrict_restrict (hMm l).measurableSet, inter_comm] using hh
  obtain ⟨f₀, heqM, heqK, k, F, r, g, V, φ, φi, hk, hF, hretain, hrpos, hg, hPD,
      hcore, hfar, htail, hlocal, hV, heq, hconf, hnorm, htrans, henergy⟩ :=
    principal_subordinate_graph_transfer (ε := ε) hcompact hfinite D.H D.disjoint_closures hn
      (fun j => realJordanInterior (H j)) (fun j => (realJordanInterior_geometry (H j)).1)
      (pairwise_disjoint_realJordan_closures H hHd)
      (fun j => (realJordanInterior_geometry (H j)).2.1)
      (fun j => (realJordanInterior_geometry (H j)).2.2) (isOpen_realChartDomain hG)
      hK hKc hKG hKQ (real_completedRegion_subset_extension D.H H G (π '' Gᶜ) π hbad hcov)
      (real_core_avoids_filling H (sphericalCore_subset_cutoffCore χ hχzero) hHC)
      Mm hMm hbd f hf h2 χ hχ hχzero L (fun l i => realChartDomain (π ⁻¹' P l i)) vp hvp hproj
      Nbh (fun j => (hNbh j).1) (fun j => (hNbh j).2) hbranches hBG hBK hBχ
      R qr hgraph N θ hgrid hvi (hgood.mono fun k hk => hk.trans (by linarith)) k₀
  let Q : MaskedModelData D.H H (realChartDomain G) K Mm f χ N θ ε := {
    widthIndex := k, base := f₀, base_mask := heqM, base_core := heqK,
    functions := F, filled := hF,
    extension_contains := real_completedRegion_subset_extension D.H H G (π '' Gᶜ) π hbad hcov,
    mask_boundary_core := hbd, retained := hretain, radius := r, radius_pos := hrpos,
    metric := g, metric_smooth := hg, metric_pos := hPD, metric_core := hcore, metric_far := hfar,
    tail := htail, localized := hlocal, domain := V, forward := φ, inverse := φi,
    circle_domain := hV, equivalence := heq, conformal_core := hconf, principal := hnorm,
    transported := htrans, transported_energy := henergy }
  exact ⟨K, χ, N, θ, hfin, D, m, H, Q, hk, hK, hK₀K, hKG, hKc, hKQ, hbd,
    hχ, hχzero, hD, hDH, hN, hcard, hosc⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
