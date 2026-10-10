import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.MovingHessianLimit
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearCompact
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearMatrix
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearClose

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section CenterDetCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance centerDetDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance centerDetDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance centerDetBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance centerDetBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

lemma exists_center_matrix_limit {V C:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {C₀:E →L[ℝ] E →L[ℝ] ℝ} {a:ℕ → ℝ} {a₀ k₀:ℝ}
    (hC:Tendsto C atTop (𝓝 C₀)) (ha:Tendsto a atTop (𝓝 a₀)) (hk:0<k₀)
    (hV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0 ≤ V j d d) ∧ (∀d,V j d d ≤ C j d d) ∧
      0 ≤ a j ∧ k₀ ≤ a j*(bilinearOperator (V j)).det) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧ (∀d e,V₀ d e=V₀ e d) ∧
      (∀d,d≠0 → 0<V₀ d d) ∧ (∀d,V₀ d d ≤ C₀ d d) ∧
      0<a₀ ∧ k₀ ≤ a₀*(bilinearOperator V₀).det := by
  have hCn : Tendsto (fun j => ‖C j‖) atTop (𝓝 ‖C₀‖) := hC.norm
  have hCb:∀ᶠ j in atTop,‖C j‖≤‖C₀‖+1:=by
    filter_upwards [hCn.eventually (gt_mem_nhds (show ‖C₀‖<‖C₀‖+1 by linarith))] with j hj
    exact hj.le
  have hbound:∀ᶠ j in atTop,‖V j‖≤‖C₀‖+1:=by
    filter_upwards [hCb,hV] with j hj hv
    apply symmetric_bilinear_norm_bound hv.1 (by positivity)
    intro d
    rw [abs_of_nonneg (hv.2.1 d)]
    calc
      V j d d ≤ C j d d:=hv.2.2.1 d
      _ ≤ |C j d d|:=le_abs_self _
      _ ≤ ‖C j‖*‖d‖^2:=bilinear_quadratic_norm_bound _ _
      _ ≤ (‖C₀‖+1)*‖d‖^2:=mul_le_mul_of_nonneg_right hj (sq_nonneg _)
  obtain ⟨V₀,σ,hσ,HV⟩:=exists_bilinear_limit hbound
  have hve:=hσ.tendsto_atTop.eventually hV
  have hvs:∀d e,V₀ d e=V₀ e d:=bilinear_limit_symm HV (hve.mono (fun j hj=>hj.1))
  have hvp:∀d,0≤V₀ d d:=bilinear_limit_nonneg HV (hve.mono (fun j hj=>hj.2.1))
  have hae:0≤a₀:=ge_of_tendsto (ha.comp hσ.tendsto_atTop) (hve.mono (fun j hj=>hj.2.2.2.1))
  have hdet:k₀≤a₀*(bilinearOperator V₀).det:=ge_of_tendsto
    ((ha.comp hσ.tendsto_atTop).mul (bilinear_det_tendsto HV)) (hve.mono (fun j hj=>hj.2.2.2.2))
  have hdp:0 < (bilinearOperator V₀).det:=by
    have H:=bilinear_det_nonneg hvs hvp
    nlinarith only [hk,hdet,hae,H]
  have hap:0<a₀:=by nlinarith only [hk,hdet,hae,hdp]
  refine ⟨V₀,σ,hσ,HV,hvs,bilinear_positive_of_det_ne_zero hvs hvp hdp.ne',?_,hap,hdet⟩
  intro d
  exact le_of_tendsto_of_tendsto
    (tendsto_clm_apply (tendsto_clm_apply HV tendsto_const_nhds) tendsto_const_nhds)
    (tendsto_clm_apply (tendsto_clm_apply (hC.comp hσ.tendsto_atTop) tendsto_const_nhds) tendsto_const_nhds)
    (hve.mono (fun j hj=>hj.2.2.1 d))

lemma exists_center_matrix_limit_variable {V C:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {C₀:E →L[ℝ] E →L[ℝ] ℝ} {a k:ℕ → ℝ} {a₀ k₀:ℝ}
    (hC:Tendsto C atTop (𝓝 C₀)) (ha:Tendsto a atTop (𝓝 a₀))
    (hk:Tendsto k atTop (𝓝 k₀)) (hk0:0<k₀)
    (hV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0 ≤ V j d d) ∧ (∀d,V j d d ≤ C j d d) ∧
      0 ≤ a j ∧ k j ≤ a j*(bilinearOperator (V j)).det) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧ (∀d e,V₀ d e=V₀ e d) ∧
      (∀d,d≠0 → 0<V₀ d d) ∧ (∀d,V₀ d d ≤ C₀ d d) ∧
      0<a₀ ∧ k₀ ≤ a₀*(bilinearOperator V₀).det := by
  have HV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0 ≤ V j d d) ∧ (∀d,V j d d ≤ C j d d) ∧
      0 ≤ a j ∧ k₀/2 ≤ a j*(bilinearOperator (V j)).det:=by
    filter_upwards [hV,hk.eventually (lt_mem_nhds (show k₀/2<k₀ by linarith))] with j hj hkj
    exact ⟨hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hkj.le.trans hj.2.2.2.2⟩
  obtain ⟨V₀,σ,hσ,HV,hVs,hVp,hVC,ha0,_⟩:=
    exists_center_matrix_limit hC ha (half_pos hk0) HV
  refine ⟨V₀,σ,hσ,HV,hVs,hVp,hVC,ha0,?_⟩
  exact le_of_tendsto_of_tendsto (hk.comp hσ.tendsto_atTop)
    ((ha.comp hσ.tendsto_atTop).mul (bilinear_det_tendsto HV))
    ((hσ.tendsto_atTop.eventually hV).mono (fun j hj=>hj.2.2.2.2))
end CenterDetCompact
end WeakMTWTransport

end
end

end OAI
