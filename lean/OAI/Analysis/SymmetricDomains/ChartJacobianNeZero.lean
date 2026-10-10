import Mathlib
import OAI.Analysis.SymmetricDomains.EventualEquicontinuityOpenSubset

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
namespace Release061
open Set Filter Metric
open scoped Topology

theorem IsSmooth.montel_expanding {n m : ℕ} {S : Set (Affine n)}
    (hS : IsSmooth S) (f : ℕ → Affine n → Affine m)
    (hlocal : ∀ p : S, ∃ V : Set (Affine n), V ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' V) ∧ p.val ∈ V ∧
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ j in atTop,
        HolomorphicOnSubset V (fun x => f j x) ∧ ∀ y ∈ V, ‖f j y‖ ≤ M) :
    ∃ g : Affine n → Affine m, HolomorphicOnSubset S (fun x => g x) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun j => f (φ j)) g atTop S := by
  classical
  have hequi : ∀ p : S, ∀ ε, 0 < ε → ∃ A : Set S, A ∈ 𝓝 p ∧
      ∀ᶠ j in atTop, ∀ q ∈ A, dist (f j q.val) (f j p.val) < ε := by
    intro p ε hε
    obtain ⟨V,hVS,hVo,hpV,M,_,he⟩ := hlocal p
    obtain ⟨d,W,hWV,hWo,hpW,D,hD,⟨e⟩⟩ :=
      smoothAtSubset_restrict_open hVS hVo hpV (hS p)
    apply eventual_equicontinuity_of_open_subset (hWV.trans hVS)
      (relative_open_trans hVS hWV hVo hWo) hpW
    apply chart_eventual_equicontinuity (M := M) hD e _ (⟨p.val,hpW⟩ : W) hε
    exact he.mono fun j hj => ⟨hj.1.restrict hWV,fun y hy => hj.2 y (hWV hy)⟩
  have hcompact : ∀ p : S, ∃ K : Set (Affine m), IsCompact K ∧
      ∀ j, f j p.val ∈ K := by
    intro p
    obtain ⟨V,_,_,hpV,M,hM,he⟩ := hlocal p
    exact compact_range_of_eventually_norm_le hM (he.mono fun j hj => hj.2 p.val hpV)
  obtain ⟨g,_,φ,hφ,hconv⟩ :=
    locally_uniform_subsequence_of_eventual_equicontinuity
      (fun j (p : S) => f j p.val) hequi hcompact
  let G := ambientExtend g
  have hc : TendstoLocallyUniformlyOn (fun j => f (φ j)) G atTop S := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa only [Function.comp_def,G,ambientExtend,dite_eq_left (Subtype.prop _)] using hconv
  refine ⟨G,?_,φ,hφ,hc⟩
  apply hS.holomorphic_locally_uniform_limit hc
  intro p
  obtain ⟨V,hVS,hVo,hpV,M,hM,he⟩ := hlocal p
  exact ⟨V,hVS,hVo,hpV,hφ.tendsto_atTop (he.mono fun j hj => hj.1)⟩

theorem chart_jacobian_ne_zero_of_left_inverse {n m : ℕ}
    {W : Set (Affine n)} {D O : Set (Affine m)}
    (hD : IsOpen D) (hO : IsOpen O) (e : Biholomorph W D)
    {F : Affine n → Affine m} {G : Affine m → Affine n}
    (hF : HolomorphicOnSubset W (fun x => F x))
    (hG : AnalyticOnNhd ℂ G O)
    (hleft : ∀ q ∈ W, F q ∈ O → G (F q) = q)
    (q : W) (hqO : F q.val ∈ O) :
    (fderiv ℂ (F ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val))
      (e.toHomeomorph q).val).det ≠ 0 := by
  let z := (e.toHomeomorph q).val
  let E := ambientExtend (fun x : D => (e.toHomeomorph.symm x).val)
  let H := F ∘ E
  have hz : z ∈ D := (e.toHomeomorph q).property
  have hEq : E z = q.val := by
    dsimp only [E,z]
    rw [ambientExtend_apply _ (e.toHomeomorph q),e.toHomeomorph.symm_apply_apply]
  have hHz : H z = F q.val := congrArg F hEq
  have hHa : AnalyticAt ℂ H z := analytic_comp_chart_inverse hD e hF z hz
  have hEa : AnalyticAt ℂ E z :=
    e.holomorphic_invFun.analyticOnNhd_extend hD z hz
  obtain ⟨A,hAo,hqA,φ,hφ,hext⟩ := e.holomorphic_toFun q
  have hφa : AnalyticAt ℂ φ (G (H z)) := by
    rw [hHz,hleft q q.property hqO]
    exact hφ q.val hqA
  have hGa : AnalyticAt ℂ G (H z) := by rw [hHz]; exact hG _ hqO
  have hideq : (φ ∘ G ∘ H) =ᶠ[𝓝 z] id := by
    have hEA : ∀ᶠ x in 𝓝 z, E x ∈ A := by
      apply hEa.continuousAt.preimage_mem_nhds
      rw [hEq]
      exact hAo.mem_nhds hqA
    have hHO : ∀ᶠ x in 𝓝 z, H x ∈ O := by
      apply hHa.continuousAt.preimage_mem_nhds
      rw [hHz]
      exact hO.mem_nhds hqO
    filter_upwards [hD.mem_nhds hz,hEA,hHO] with x hx hxA hxO
    have hEx : E x = (e.toHomeomorph.symm ⟨x,hx⟩).val := ambientExtend_apply _ ⟨x,hx⟩
    have hEW : E x ∈ W := hEx ▸ (e.toHomeomorph.symm ⟨x,hx⟩).property
    change φ (G (F (E x))) = x
    rw [hleft (E x) hEW hxO]
    rw [hEx] at hxA ⊢
    rw [hext (e.toHomeomorph.symm ⟨x,hx⟩) hxA]
    exact congrArg Subtype.val (e.toHomeomorph.apply_symm_apply ⟨x,hx⟩)
  have hd := ((hφa.differentiableAt.hasFDerivAt.comp (H z)
      hGa.differentiableAt.hasFDerivAt).comp z hHa.differentiableAt.hasFDerivAt).unique
      ((hasFDerivAt_id z).congr_of_eventuallyEq hideq)
  have hdet := congrArg ContinuousLinearMap.det hd
  change LinearMap.det
      (((fderiv ℂ φ (G (H z))).toLinearMap.comp (fderiv ℂ G (H z)).toLinearMap).comp
        (fderiv ℂ H z).toLinearMap) = LinearMap.det (LinearMap.id : Affine m →ₗ[ℂ] Affine m) at hdet
  rw [LinearMap.det_comp,LinearMap.det_id] at hdet
  intro hzero
  change LinearMap.det (fderiv ℂ H z).toLinearMap = 0 at hzero
  rw [hzero,mul_zero] at hdet
  exact zero_ne_one hdet

end Release061

end

end OAI
