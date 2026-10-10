import OAI.Analysis.CircleDomains.Topology.CoreCutoff
import OAI.Analysis.CircleDomains.Sobolev.SmoothContours

namespace OAI

/-!
# A regular retained core containing infinity

Only the already stated planar Sard input is used for the regular value.
The core may contain an arbitrary closed subset of the domain. Its
complement has compact closure in the finite chart, so the core retains
an entire neighborhood of infinity.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Manifold

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_real_regular_value_in_interval (hsard : SmoothPlanarSard)
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, ∀ z, f z = t → fderiv ℝ f z ≠ 0 := by
  let e := Complex.equivRealProdCLM
  let g : ℂ → ℝ := f ∘ e
  have hg : ContDiff ℝ ∞ g := hf.comp e.contDiff
  have hgc : HasCompactSupport g := hcompact.comp_homeomorph e.toHomeomorph
  obtain ⟨t, ht, hregular⟩ := exists_regular_value_in_interval hsard hg hgc hab
  refine ⟨t, ht, ?_⟩
  intro z hz hzero
  apply hregular (e.symm z) (by simpa only [g, Function.comp_apply, e.apply_symm_apply] using hz)
  change fderiv ℝ (f ∘ e) (e.symm z) = 0
  rw [fderiv_comp (e.symm z) (hf.differentiable (by simp) _) e.differentiableAt,
    e.fderiv, e.apply_symm_apply, hzero, ContinuousLinearMap.zero_comp]

theorem exists_smooth_real_cutoff
    {A O : Set (ℝ × ℝ)} (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ f : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧ (∀ᶠ z in 𝓝ˢ A, f z = 1) := by
  obtain ⟨V, hV, hAV, hVO, hVc⟩ := exists_open_between_and_isCompact_closure hA hO hAO
  obtain ⟨f, hzero, hone, hrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, ℝ × ℝ)) hV.isClosed_compl hA.isClosed
    (disjoint_compl_left_iff_subset.mpr hAV) (n := (⊤ : ℕ∞))
  have hsupport : support (f : (ℝ × ℝ) → ℝ) ⊆ V := by
    intro z hz
    by_contra hzV
    exact hz (hzero.self_of_nhdsSet z hzV)
  have hts : tsupport (f : (ℝ × ℝ) → ℝ) ⊆ closure V := closure_mono hsupport
  exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff,
    hVc.of_isClosed_subset isClosed_closure hts, hts.trans hVO, hrange, hone⟩

/-- Sard selects a regular level separating a prescribed closed part of
the physical domain from all its complementary components. Finite
energy makes the remaining tail small. -/
theorem exists_regular_core_small_tail (hsard : SmoothPlanarSard)
    {G K₀ : Set (ℝ × ℝ)} (hG : IsOpen G) (hGc : IsCompact Gᶜ)
    (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ G)
    {f : (ℝ × ℝ) → ℝ} (hf : IntegrableOn f G) (hf0 : ∀ z, 0 ≤ f z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ψ : (ℝ × ℝ) → ℝ) (t : ℝ) (K : Set (ℝ × ℝ)),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ t ∈ Ioo 0 1 ∧
      (∀ z, ψ z = t → fderiv ℝ ψ z ≠ 0) ∧ K = {z | ψ z ≤ t} ∧
      IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧ IsCompact (closure Kᶜ) ∧
      (∫ z in G \ K, f z) < ε := by
  obtain ⟨A, hAc, _, hAG, htail⟩ := exists_compact_core_small_tail hG isCompact_empty
    (empty_subset G) hf hf0 hε
  have hB : IsClosed (K₀ ∪ A) := hK₀.union hAc.isClosed
  have hBG : K₀ ∪ A ⊆ G := union_subset hK₀G hAG
  obtain ⟨ψ, hψ, hψc, hψsupp, _, hone⟩ := exists_smooth_real_cutoff hGc hB.isOpen_compl
    (fun z hzG hzB => hzG (hBG hzB))
  obtain ⟨t, ht, hreg⟩ := exists_real_regular_value_in_interval hsard hψ hψc zero_lt_one
  let K : Set (ℝ × ℝ) := {z | ψ z ≤ t}
  have hzero (z : ℝ × ℝ) (hz : z ∈ K₀ ∪ A) : ψ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hψsupp hs hz)
  have hBK : K₀ ∪ A ⊆ K := fun z hz => by
    change ψ z ≤ t
    rw [hzero z hz]
    exact ht.1.le
  have hclosed : IsClosed K := isClosed_le hψ.continuous continuous_const
  have hcore : K₀ ⊆ interior K := by
    have hsmall : {z | ψ z < t} ⊆ interior K := by
      apply interior_maximal ?_ (isOpen_lt hψ.continuous continuous_const)
      intro z hz
      change ψ z ≤ t
      exact hz.le
    intro z hz
    apply hsmall
    change ψ z < t
    rw [hzero z (Or.inl hz)]
    exact ht.1
  have hKG : K ⊆ G := by
    intro z hz
    by_contra hzG
    have h1 := hone.self_of_nhdsSet z hzG
    have hle : ψ z ≤ t := hz
    rw [h1] at hle
    exact (not_le.mpr ht.2) hle
  have hsupp : Kᶜ ⊆ tsupport ψ := by
    intro z hz
    apply subset_tsupport
    change ψ z ≠ 0
    intro heq
    apply hz
    change ψ z ≤ t
    rw [heq]
    exact ht.1.le
  refine ⟨ψ, t, K, hψ, hψc, ht, hreg, rfl, hclosed, hcore, hKG,
    hψc.of_isClosed_subset isClosed_closure (closure_minimal hsupp (isClosed_tsupport ψ)), ?_⟩
  apply lt_of_le_of_lt _ htail
  apply setIntegral_mono_set (hf.mono_set sdiff_subset) (Eventually.of_forall hf0)
  exact Eventually.of_forall (fun z hz => ⟨hz.1, fun hzA => hz.2 (hBK (Or.inr hzA))⟩)

/-- For a domain containing infinity the cutoff is compactly supported
in the finite chart, vanishes near the entire retained core and equals
one near every missing component. -/
theorem exists_cutoff_near_complement
    {G K : Set (ℝ × ℝ)} (hGc : IsCompact Gᶜ) (hK : IsClosed K) (hKG : K ⊆ G) :
    ∃ χ : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ z, χ z ∈ Icc 0 1) ∧ (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧
      (∀ᶠ z in 𝓝ˢ Gᶜ, χ z = 1) ∧ MemLp (planarGradient χ) 2 volume := by
  obtain ⟨χ, hχ, hχc, hsupport, hrange, hone⟩ := exists_smooth_real_cutoff hGc hK.isOpen_compl
    (fun z hzG hzK => hzG (hKG hzK))
  refine ⟨χ, hχ, hχc, hrange, ?_, hone,
    (continuous_planarGradient hχ).memLp_of_hasCompactSupport (hasCompactSupport_planarGradient hχc)⟩
  apply eventually_nhdsSet_iff_forall.mpr
  intro z hz
  exact notMem_tsupport_iff_eventuallyEq.mp (fun hs => hsupport hs hz)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
