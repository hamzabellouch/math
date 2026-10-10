import Mathlib
import OAI.Analysis.SymmetricDomains.NoncollapsedSupportedBoundary
import OAI.Analysis.SymmetricDomains.Cutoff
import OAI.Analysis.SymmetricDomains.Local
import OAI.Analysis.SymmetricDomains.IndependentSupportRows
import OAI.Analysis.SymmetricDomains.GlobalTwoSided

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

theorem original_global_quadratic_scaling {N : ℕ} (V U : Set (Affine N))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (r k l : ℕ) (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
      (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ))
      (f : (Fin l → ℝ) → ℝ) (a : Fin k → ℝ),
      1 ≤ k ∧ LipschitzWith 1 f ∧ f 0 = 0 ∧
      (∀ t : ℝ, 0 < t → ∀ y, f y = 0 ↔ f (t • y) = 0) ∧ f (L a) ≠ 0 ∧
      Nonempty (Biholomorph U (connectedComponentIn
        ((affineProductCoordinates r k) ''
          {z : Affine r × Affine k | f (L (Flatten.imaginaryPart k z.2)+Q (fun _ => z.1)) ≠ 0})
        ((affineProductCoordinates r k) (0,fun i => Complex.I*(a i : ℂ))))) := by
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
  obtain ⟨_hnew,β,hβ,hβeq⟩ := s.independent_support_rows hcgood hcut hq hqi hr
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
  refine ⟨s.tangentDim,s.normalDim,c.normal.normalDim,s.normalMap,Q,f,a,hk,hfl,hf0,hfcone,?_,hglob⟩
  simpa only [a,s.normalMap.apply_symm_apply] using hv

end Release061

end

end OAI
