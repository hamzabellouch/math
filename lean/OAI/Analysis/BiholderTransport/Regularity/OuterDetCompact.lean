import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearMatrix
import OAI.Analysis.BiholderTransport.LinearAlgebra.PositiveDetCompact

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section OuterDetCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance outerDetDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance outerDetDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance outerDetBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance outerDetBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

lemma exists_outer_matrix_limit {V B:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {B₀:E →L[ℝ] E →L[ℝ] ℝ} {a k:ℕ → ℝ} {a₀ k₀:ℝ}
    (hB:Tendsto B atTop (𝓝 B₀)) (ha:Tendsto a atTop (𝓝 a₀))
    (hk:Tendsto k atTop (𝓝 k₀)) (ha0:0 < a₀)
    (hpos:∀d,d≠0 → 0 < B₀ d d)
    (hV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0 ≤ V j d d) ∧ (∀d,B j d d ≤ V j d d) ∧
      a j*(bilinearOperator (V j)).det ≤ k j) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧ (∀d e,V₀ d e=V₀ e d) ∧
      (∀d,d≠0 → 0 < V₀ d d) ∧ (∀d,B₀ d d ≤ V₀ d d) ∧
      a₀*(bilinearOperator V₀).det ≤ k₀ := by
  let K:=2*(|k₀|+1)/a₀
  have hK:0 ≤ K:=by dsimp only [K]; positivity
  have hbound:∀ᶠ j in atTop,|(bilinearOperator (V j)).det| ≤ K:=by
    filter_upwards [hV,ha.eventually (lt_mem_nhds (show a₀/2<a₀ by linarith)),
      hk.eventually (gt_mem_nhds (show k₀ < |k₀|+1 from lt_of_le_of_lt (le_abs_self k₀) (by linarith)))]
      with j hj haj hkj
    have hd:=bilinear_det_nonneg hj.1 hj.2.1
    rw [abs_of_nonneg hd]
    have H:(a₀/2)*(bilinearOperator (V j)).det≤|k₀|+1:=
      (mul_le_mul_of_nonneg_right haj.le hd).trans (hj.2.2.2.trans hkj.le)
    dsimp only [K]
    apply (le_div_iff₀ ha0).mpr
    nlinarith only [H]
  obtain ⟨V₀,σ,hσ,HV,hVs,hlo,hp⟩:=exists_bilinear_limit_of_det_lower hB hpos
    (hV.mono (fun j hj=>⟨hj.1,hj.2.2.1⟩)) hK hbound
  refine ⟨V₀,σ,hσ,HV,hVs,hp,hlo,?_⟩
  exact le_of_tendsto_of_tendsto
    ((ha.comp hσ.tendsto_atTop).mul (bilinear_det_tendsto HV)) (hk.comp hσ.tendsto_atTop)
    ((hσ.tendsto_atTop.eventually hV).mono (fun j hj=>hj.2.2.2))
end OuterDetCompact
end WeakMTWTransport

end
end

end OAI
