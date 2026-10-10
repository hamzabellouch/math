import Mathlib
import OAI.Analysis.SymmetricDomains.NoncollapsedSupportedBoundary
import OAI.Analysis.SymmetricDomains.Cutoff
import OAI.Analysis.SymmetricDomains.Local
import OAI.Analysis.SymmetricDomains.IndependentSupportRows
import OAI.Analysis.SymmetricDomains.GlobalTwoSided
import OAI.Analysis.SymmetricDomains.RawQuadraticModelNormalization
import OAI.Analysis.SymmetricDomains.SupportedHermitianWeightedModel

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem original_supported_hermitian_model {N : ℕ} (V U : Set (Affine N))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (r k : ℕ) (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ)
      (C : Set (Fin k → ℝ)) (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (c : ℝ),
      1 ≤ k ∧ IsOpen C ∧ IsConnected C ∧ (0 : Fin k → ℝ) ∉ C ∧
      (∀ t : ℝ, 0 < t → ∀ y, t • y ∈ C ↔ y ∈ C) ∧ 0 < c ∧
      (∀ z ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
        ∀ i, c*‖z.1‖^2 ≤ e (fun j => (z.2 j).im) i) ∧
      Nonempty (Biholomorph U
        ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)) := by
  let : LocallyCompactSpace U := locallyCompact_of_relative_open hV hUV hU
  have hsm := cocompact_bounded_affine_smooth V U hV hUV hU hc hb Γ hhol
  let V' := MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)
  have hUV' : U ⊆ V' := fun z hz p hp => hp z hz
  have hV'V : V' ⊆ V := by
    obtain ⟨R,hR⟩ := hV
    intro z hz
    rw [hR]
    intro p hp
    exact hz p (fun y hy => (hR ▸ hUV hy) p hp)
  have hU' : IsOpen ((Subtype.val : V' → Affine N) ⁻¹' U) :=
    hU.preimage (continuous_inclusion hV'V)
  have hV'closed : IsClosed V' := zeroLocus_closed _
  obtain ⟨m,C,hC⟩ := original_noncollapsed_supported_boundary V U hV hUV hU hc hn hb hs Γ hhol
  obtain ⟨p,x,k,F,G,h,hxp,_hxb,hbd,hgood,hk,hkm,hdk,hF0,hF,hG,hGF,hFG,hFV,hgen,
    hha,hh0,hpeak,hlog,hI,_hCI,hzero⟩ := hC (fun _ => ∅) (fun _ => measure_empty)
  obtain ⟨c,hcgood,_hslope,hproper⟩ := hgood
  have hq := (p.val.analytic_complexMap x hxp).differentiableAt
  have hqi := p.val.injective_fderiv_complexMap hxp
  have hr := coordinate_rank_ge_of_chart_generic p.val.complexMap G hG hq hgen
  obtain ⟨s₀⟩ := c.scaling_chart hcgood hq hqi hr
  obtain ⟨s₁,_hs₁t,_hs₁n,hcut₁⟩ := s₀.exists_cutoff hcgood
  have hpxV' : p.val.complexMap x ∈ V' := hV'closed.closure_subset_iff.mpr hUV' hbd.1
  obtain ⟨s,_hst,_hsn,hcut,Ω,hΩV,hΩo,hpΩ,hfΩ,hgS,hfg⟩ :=
    s₁.exists_local_chart hcgood hcut₁ hpxV' F G hF0 hF hG hGF hFG
  have hnk : s.normalDim=k := by
    have h1 := c.normal.real_dimension
    have h2 := c.normal.complex_dimension
    have h3 := s.normal_dimension
    omega
  subst k
  obtain ⟨hnew,β,hβ,hβeq⟩ := s.independent_support_rows hcgood hcut hq hqi hr
    F G hF0 hF hG hGF hFG hFV h hlog hI hzero
  obtain ⟨f,hfl,hfb,hft,_hfut,_hfclosed,hf0,hfcone⟩ := hcgood.2.2.2
  obtain ⟨Q,hcov,hexc⟩ := s.two_sided hcgood f hft (fun y => (hfb y).1)
  have hfne : ∃ v, f v ≠ 0 := by
    by_contra! hall
    apply hproper f hft
    ext y
    simp only [mem_ofPred_eq,mem_univ,iff_true]
    exact hall y
  obtain ⟨v,hv⟩ := hfne
  let a := s.normalMap.symm v
  let w : Affine s.normalDim := fun i => Complex.I*(a i : ℂ)
  let R : Affine s.tangentDim × Affine s.normalDim → Fin c.normal.normalDim → ℝ :=
    fun z => s.normalMap (Flatten.imaginaryPart s.normalDim z.2)+Q (fun _ => z.1)
  let O : Set (Affine s.tangentDim × Affine s.normalDim) := {z | f (R z) ≠ 0}
  have hRc : Continuous R := by
    apply Continuous.add
    · exact s.normalMap.continuous.comp ((Flatten.imaginaryPart s.normalDim).continuous.comp continuous_snd)
    · exact Q.cont.comp (continuous_pi fun _ => continuous_fst)
  have hOo : IsOpen O := isOpen_ne_fun (hfl.continuous.comp hRc) continuous_const
  have hw : (0,w) ∈ O := by
    have hQ0 : Q (fun _ : Fin 2 => (0 : Affine s.tangentDim))=0 := Q.map_zero
    have hwim : Flatten.imaginaryPart s.normalDim w=a := by
      ext i
      simp [Flatten.imaginaryPart,w]
    change f (s.normalMap (Flatten.imaginaryPart s.normalDim w)+Q (fun _ => 0)) ≠ 0
    rw [hQ0,add_zero,hwim]
    simpa only [a,s.normalMap.apply_symm_apply] using hv
  have hhb : ∀ i y, y ∈ U → ‖h i y‖ ≤ 1 := by
    intro i y hy
    exact (hpeak i y (subset_closure hy)).trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  have hpk : ∀ y ∈ U, ‖h (⟨0,by omega⟩ : Fin s.normalDim) y‖ ≤
      Real.exp (-(‖y-p.val.complexMap x‖^2)) := by
    intro y hy
    simpa only [dist_eq_norm] using hpeak ⟨0,by omega⟩ y (subset_closure hy)
  have hcover : ∀ K, IsCompact K → K ⊆ O → ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ s.domain t := by
    intro K hK hKO
    simpa only [s.domain_eq hcut] using hcov K hK hKO
  have hexclude : ∀ z ∉ O, ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
      ∃ y : ℕ → Affine s.tangentDim × Affine s.normalDim,
        Tendsto y atTop (𝓝 z) ∧ ∀ᶠ j in atTop, y j ∉ s.domain (t j) := by
    intro z hz t ht htp
    have hz' : f (R z)=0 := not_not.mp hz
    obtain ⟨y,hy,hey,_hchart⟩ := hexc z hz' t ht htp
    refine ⟨y,hy,Eventually.of_forall fun j => ?_⟩
    simpa only [s.domain_eq hcut] using hey j
  have hglob := s.global_from_two_sided hcgood hcut hUV' hU' hc hb hsm Γ hhol
    Ω hΩV hΩo hpΩ hfΩ hgS hfg h
    (fun i y => (hha i y (mem_univ _)).differentiableAt) hh0 hhb
    ⟨0,by omega⟩ hpk β hβ hβeq O hOo w hw hcover hexclude
  let L := s.normalMap
  let B₀ := residualQuadraticCoefficients L Q
  let H : Affine s.tangentDim → Fin s.normalDim → ℝ := fun z i => B₀ i z z
  let C₀ : Set (Fin s.normalDim → ℝ) := {y | f (L y) ≠ 0}
  let C := connectedComponentIn C₀ a
  let e₀ := affineProductCoordinates s.tangentDim s.normalDim
  have ha : a ∈ C₀ := by
    change f (s.normalMap (s.normalMap.symm v)) ≠ 0
    simpa only [s.normalMap.apply_symm_apply] using hv
  have hH : Continuous H := residualQuadraticCoefficients_continuous L Q
  have hH0 : H 0=0 := residualQuadraticCoefficients_zero L Q
  have hC₀ : IsOpen C₀ := isOpen_ne_fun (hfl.continuous.comp L.continuous) continuous_const
  have hcone₀ : ∀ t : ℝ, 0 < t → ∀ y ∈ C₀, t • y ∈ C₀ := by
    intro t ht y hy
    change f (L (t • y)) ≠ 0
    rw [map_smul]
    exact (hfcone t ht (L y)).not.mp hy
  obtain ⟨hCo,hCc,hCcone⟩ := open_cone_component hC₀ hcone₀ ha
  have hCzero : (0 : Fin s.normalDim → ℝ) ∉ C := by
    intro h
    have h' := connectedComponentIn_subset C₀ a h
    exact h' (by simpa only [map_zero,mem_ofPred_eq] using hf0)
  have hp : (0,w) ∈ quadraticDomain H C₀ := quadraticDomain_axis H hH0 ha
  have hpa : (fun i => (w i).im-H 0 i)=a := by
    simp only [w,hH0,Pi.zero_apply,sub_zero,Complex.I_mul_im,Complex.ofReal_re]
  have hraw : O=quadraticDomain H C₀ := by
    ext z
    have he : L (Flatten.imaginaryPart s.normalDim z.2-H z.1)=
        L (Flatten.imaginaryPart s.normalDim z.2)+Q (fun _ => z.1) := by
      rw [show H z.1= -L.symm (Q (fun _ => z.1)) from residualQuadraticCoefficients_diag L Q z.1,
        sub_neg_eq_add,map_add,L.apply_symm_apply]
    change f (L (Flatten.imaginaryPart s.normalDim z.2)+Q (fun _ => z.1)) ≠ 0 ↔
      f (L (Flatten.imaginaryPart s.normalDim z.2-H z.1)) ≠ 0
    rw [he]
  have hcc : connectedComponentIn (e₀ '' O) (e₀ (0,w)) =
      e₀ '' quadraticDomain H C := by
    rw [hraw]
    change connectedComponentIn (e₀.toHomeomorph '' quadraticDomain H C₀) (e₀.toHomeomorph (0,w)) = _
    rw [← e₀.toHomeomorph.image_connectedComponentIn hp,
      quadraticDomain_connectedComponent H hH C₀ (0,w),hpa]
    rfl
  have hrawsub : quadraticDomain H C ⊆ O := by
    rw [hraw]
    intro z hz
    exact connectedComponentIn_subset C₀ a hz
  have hcover₀ : ∀ z ∈ quadraticDomain H C,
      ∀ᶠ t : ℝ in 𝓝[>] 0, s.forward (weightedScale t z) ∈ U := by
    intro z hz
    have hh := hcover {z} (isCompact_singleton) (singleton_subset_iff.mpr (hrawsub hz))
    filter_upwards [hh] with t ht
    exact (ht (mem_singleton z)).2
  have hΦ := s.forward_analytic hcut 0 s.source_zero
  have hΨ := s.backward_analytic (q := p.val.complexMap) (p.val.complexMap x) (mem_univ _)
  have hbgf : (s.backward ∘ s.forward) =ᶠ[𝓝 (0 : Affine s.tangentDim × Affine s.normalDim)] id := by
    filter_upwards [s.offsets.open_source.mem_nhds s.source_zero] with z hz
    exact s.backward_forward hcut hz
  have hleft : (fderiv ℂ s.backward (p.val.complexMap x)).comp (fderiv ℂ s.forward 0)=1 := by
    have hd := ((s.forward_zero hcgood).symm ▸ hΨ.differentiableAt.hasFDerivAt).comp 0 hΦ.differentiableAt.hasFDerivAt
    have hd' := hd.congr_of_eventuallyEq hbgf.symm
    simpa only [s.forward_zero hcgood,fderiv_id,ContinuousLinearMap.one_def] using hd'.fderiv.symm
  have hΦi : Function.Injective (fderiv ℂ s.forward 0) := by
    intro z z' hz
    have H := congrArg (fderiv ℂ s.backward (p.val.complexMap x)) hz
    simpa only [←ContinuousLinearMap.comp_apply,hleft,one_apply_eq_self] using H
  obtain ⟨e,c₀,hc₀,hbounds⟩ := supported_hermitian_weighted_model B₀ C s.forward hΦ hΦi U
    hcover₀ h (fun i => by simpa only [s.forward_zero hcgood] using (hha i _ (mem_univ _)).continuousAt)
    (fun i => by simpa only [s.forward_zero hcgood] using hh0 i)
    (fun i y hy => by simpa only [s.forward_zero hcgood,dist_eq_norm] using hpeak i y (subset_closure hy))
    hnew β hβ hβeq
  obtain ⟨g⟩ := hglob
  have g' : Biholomorph U (e₀ '' quadraticDomain H C) := hcc ▸ g
  obtain ⟨shear⟩ := quadraticShear_biholomorph B₀ C
  exact ⟨s.tangentDim,s.normalDim,B₀,C,e,c₀,hk,hCo,hCc,hCzero,hCcone,hc₀,hbounds,
    ⟨g'.trans shear⟩⟩

end Release061

end

end OAI
