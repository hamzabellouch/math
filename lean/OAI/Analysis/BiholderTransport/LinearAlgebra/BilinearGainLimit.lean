import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.CenterDetCompact

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section BilinearGainLimit
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance gainDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gainDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance gainBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance gainBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

lemma rankForm_tendsto {f:ℕ → E →L[ℝ] ℝ} {g:E →L[ℝ] ℝ}
    (hf:Tendsto f atTop (𝓝 g)) :
    Tendsto (fun j=>(f j).smulRight (f j)) atTop (𝓝 (g.smulRight g)) :=
  (isBoundedBilinearMap_smulRight.continuous.continuousAt.tendsto).comp (hf.prodMk_nhds hf)

variable [FiniteDimensional ℝ E]

lemma exists_bilinear_gain_limit {V H G:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {H₀ G₀:E →L[ℝ] E →L[ℝ] ℝ} {f:ℕ → E →L[ℝ] ℝ} {f₀:E →L[ℝ] ℝ}
    {a k b c:ℕ → ℝ} {a₀ k₀ b₀ c₀:ℝ}
    (hH:Tendsto H atTop (𝓝 H₀)) (hG:Tendsto G atTop (𝓝 G₀))
    (hf:Tendsto f atTop (𝓝 f₀))
    (ha:Tendsto a atTop (𝓝 a₀)) (hk:Tendsto k atTop (𝓝 k₀))
    (hb:Tendsto b atTop (𝓝 b₀)) (hc:Tendsto c atTop (𝓝 c₀)) (hk0:0<k₀)
    (hV:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0≤V j d d) ∧ (∀d,V j d d+b j*G j d d+c j*(f j d)^2≤H j d d) ∧
      0≤a j ∧ k j≤a j*(bilinearOperator (V j)).det) :
    ∃V₀:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧
      Tendsto (V ∘ σ) atTop (𝓝 V₀) ∧ (∀d e,V₀ d e=V₀ e d) ∧
      (∀d,d≠0 → 0<V₀ d d) ∧
      (∀d,V₀ d d+b₀*G₀ d d+c₀*(f₀ d)^2≤H₀ d d) ∧
      0<a₀ ∧ k₀≤a₀*(bilinearOperator V₀).det := by
  let C:=fun j=>H j-b j • G j-c j • (f j).smulRight (f j)
  let C₀:=H₀-b₀ • G₀-c₀ • f₀.smulRight f₀
  have hC:Tendsto C atTop (𝓝 C₀):=(hH.sub (hb.smul hG)).sub (hc.smul (rankForm_tendsto hf))
  have Hvc:∀ᶠ j in atTop,(∀d e,V j d e=V j e d) ∧
      (∀d,0≤V j d d) ∧ (∀d,V j d d≤C j d d) ∧
      0≤a j ∧ k j≤a j*(bilinearOperator (V j)).det:=by
    filter_upwards [hV] with j hj
    refine ⟨hj.1,hj.2.1,?_,hj.2.2.2⟩
    intro d
    have HH:=hj.2.2.1 d
    simp only [C,sub_apply,smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul]
    nlinarith only [HH]
  obtain ⟨V₀,σ,hσ,HV,hVs,hVp,hVC,ha0,hdet⟩:=
    exists_center_matrix_limit_variable hC ha hk hk0 Hvc
  refine ⟨V₀,σ,hσ,HV,hVs,hVp,?_,ha0,hdet⟩
  intro d
  have HH:=hVC d
  simp only [C₀,sub_apply,smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul] at HH
  nlinarith only [HH]
end BilinearGainLimit
end WeakMTWTransport

end
end

end OAI
