import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryParametricDimensionLt
import OAI.Analysis.SymmetricDomains.InjectiveConormalFinrank
import OAI.Analysis.SymmetricDomains.HolomorphicSupportIndependent
import OAI.Analysis.SymmetricDomains.EntireSupports

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
open Set Filter Topology MeasureTheory
open scoped Classical

theorem original_generic_supported_boundary {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [MulAction Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (m : ℕ) (C : Finset (NashPatch (n+n))),
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ (p : C) (x : Fin p.val.dim → ℝ) (k : ℕ)
          (F : Affine m → Affine n) (G : Affine n → Affine m)
          (h : Fin k → Affine n → ℂ),
          x ∈ p.val.domain ∧ x ∉ bad p ∧ p.val.complexMap x ∈ closure U \ U ∧
          1 ≤ k ∧ k ≤ m ∧ p.val.dim + k = 2*m ∧
          F 0 = p.val.complexMap x ∧ AnalyticAt ℂ F 0 ∧
          AnalyticAt ℂ G (p.val.complexMap x) ∧
          (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
          (∀ᶠ y in 𝓝[MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)] (p.val.complexMap x), F (G y) = y) ∧
          (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)) ∧
          Submodule.span ℂ (range (fderiv ℝ (G ∘ p.val.complexMap) x)) = ⊤ ∧
          (∀ i, AnalyticOnNhd ℂ (h i) univ) ∧
          (∀ i, h i (p.val.complexMap x) = 1) ∧
          (∀ i, ∀ z ∈ closure U, ‖h i z‖ ≤ Real.exp (-(dist z (p.val.complexMap x))^2)) ∧
          (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0) ∧
          LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap) ∧
          LinearIndependent ℂ (fun i => (fderiv ℂ (fun z => Complex.log (h i (F z))) 0).toLinearMap) ∧
          ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ p.val.complexMap) x) = 0 := by
  obtain ⟨m,P,C,_hP,hC,he⟩ := original_boundary_generic_fiber V U hV hUV hU hc hn hb hs Γ hhol
  refine ⟨m,C,fun bad hbad => ?_⟩
  obtain ⟨p,c,x,hxp,hxc,hr,hPx,hxb,hpos⟩ := he bad hbad
  obtain ⟨hpbd,W,hWI,hW,hpW,B,hB,⟨e⟩⟩ := (hC p.val p.property).2 x hxp
  obtain ⟨F,G,hF0,hF,hG,hGF,hFG,hFV⟩ := e.centered_chart_germs hWI hW hB hpW
  have hq := p.val.analytic_complexMap x hxp
  have hqi := p.val.injective_fderiv_complexMap hxp
  have hqV : ∀ᶠ y in 𝓝 x, p.val.complexMap y ∈ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U) := by
    filter_upwards [p.val.isOpen_domain.mem_nhds hxp] with y hy
    obtain ⟨_,W',hWI',_,hpW',_⟩ := (hC p.val p.property).2 y hy
    exact hWI' hpW'
  have hqn : ∀ᶠ y in 𝓝 x, p.val.complexMap y ∉ U := by
    filter_upwards [p.val.isOpen_domain.mem_nhds hxp] with y hy
    exact ((hC p.val p.property).2 y hy).1.2
  have ht : Tendsto p.val.complexMap (𝓝 x)
      (𝓝[MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)] (p.val.complexMap x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq.continuousAt,hqV⟩
  have hFGq : (F ∘ G ∘ p.val.complexMap) =ᶠ[𝓝 x] p.val.complexMap := ht hFG
  obtain ⟨_hG0,_hGFd,hd,hFi⟩ := chart_tangent_identities F G p.val.complexMap hF0 hF hG hq.differentiableAt hGF hFGq
  obtain ⟨hMi,hMg⟩ := chart_parametric_generic F G p.val.complexMap hF0 hF hG hq.differentiableAt hqi hGF hFGq hr
  let M := fderiv ℝ (G ∘ p.val.complexMap) x
  let k := Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator
  have hdk : p.val.dim + k = 2*m := injective_conormal_finrank M hMi
  have hdl : p.val.dim < 2*m := boundary_parametric_dimension_lt
    (show U ⊆ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U) from
      fun u hu P hP => hP u hu) F G p.val.complexMap hpbd.1 hF0 hF hG hq hqi hGF hFG hqV hqn
  obtain ⟨h,ha,hs,hnorm,hl,hi,hz⟩ := c.entire_supports hxc hq.differentiableAt hPx hpos F hF0 hF hFi M hd
  have hic := holomorphic_support_independent M hMg (fun i z => h i (F z)) hl hi hz
  have hkm : k ≤ m := by
    have hh := hic.fintype_card_le_finrank
    simpa [Affine] using hh
  exact ⟨p,x,k,F,G,h,hxp,hxb,hpbd,by omega,hkm,hdk,hF0,hF,hG,hGF,hFG,hFV,hMg,ha,hs,hnorm,hl,hi,hic,hz⟩
end Release061

end

end OAI
