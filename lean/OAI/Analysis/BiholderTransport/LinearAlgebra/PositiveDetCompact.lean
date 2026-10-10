import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.NormDetCoercivity
import OAI.Analysis.BiholderTransport.LinearAlgebra.MovingHessianLimit
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearCompact
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearClose
import OAI.Analysis.BiholderTransport.LinearAlgebra.RankOneCoercive

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section PositiveDetCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance positiveCompactDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance positiveCompactDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance positiveCompactBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance positiveCompactBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

lemma bilinear_eventual_coercivity
    {B:ℕ → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B atTop (𝓝 B₀)) (hpos:∀d,d≠0 → 0 < B₀ d d) :
    ∃m>0,∀ᶠ k in atTop,∀d:E,m*‖d‖^2 ≤ B k d d := by
  obtain ⟨c,hc,HC⟩:=positive_bilinear_uniform_lower hpos
  have hn:Tendsto (fun k=>‖B₀-B k‖) atTop (𝓝 0):=by
    simpa only [sub_self,norm_zero] using (show Tendsto (fun k=>B₀-B k) atTop (𝓝 (B₀-B₀)) from tendsto_const_nhds.sub hB).norm
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hn.eventually (gt_mem_nhds (half_pos hc))] with k hk
  intro d
  have H:=bilinear_quadratic_close hk.le d
  nlinarith only [H,HC d]

lemma exists_bilinear_limit_of_det_lower
    {B V:ℕ → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B atTop (𝓝 B₀)) (hpos:∀d,d≠0 → 0 < B₀ d d)
    (hV:∀ᶠ k in atTop,(∀d e,V k d e=V k e d) ∧ ∀d,B k d d ≤ V k d d)
    {K:ℝ} (hK:0 ≤ K) (hdet:∀ᶠ k in atTop,|(bilinearOperator (V k)).det| ≤ K) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧
      (∀d e,V₀ d e=V₀ e d) ∧ (∀d,B₀ d d ≤ V₀ d d) ∧
      (∀d,d≠0 → 0 < V₀ d d) := by
  obtain ⟨m,hm,Hm⟩:=bilinear_eventual_coercivity hB hpos
  let C:ℝ:=(Module.finrank ℝ E:ℝ)*K/m^(Module.finrank ℝ E-1)
  have hC:0 ≤ C:=by dsimp only [C]; positivity
  have Hbound:∀ᶠ k in atTop,‖V k‖ ≤ C:=by
    filter_upwards [Hm,hV,hdet] with k hk hv hd
    have hlo:∀d:E,m*‖d‖^2 ≤ V k d d:=fun d=>(hk d).trans (hv.2 d)
    apply symmetric_bilinear_norm_bound hv.1 hC
    intro d
    rw [abs_of_nonneg ((mul_nonneg hm.le (sq_nonneg _)).trans (hlo d))]
    exact bilinear_quadratic_bound_of_det hm hlo hd d
  obtain ⟨V₀,σ,hσ,HV⟩:=exists_bilinear_limit Hbound
  have Hlower:∀d,B₀ d d ≤ V₀ d d:=by
    intro d
    exact le_of_tendsto_of_tendsto
      (tendsto_clm_apply (tendsto_clm_apply (hB.comp hσ.tendsto_atTop) tendsto_const_nhds) tendsto_const_nhds)
      (tendsto_clm_apply (tendsto_clm_apply HV tendsto_const_nhds) tendsto_const_nhds)
      (hσ.tendsto_atTop.eventually (hV.mono (fun k hk=>hk.2 d)))
  refine ⟨V₀,σ,hσ,HV,?_,Hlower,fun d hd=>(hpos d hd).trans_le (Hlower d)⟩
  exact bilinear_limit_symm HV (hσ.tendsto_atTop.eventually (hV.mono (fun k hk=>hk.1)))

end PositiveDetCompact
end WeakMTWTransport

end
end

end OAI
