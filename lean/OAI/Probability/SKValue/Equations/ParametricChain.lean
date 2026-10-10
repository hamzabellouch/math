import Mathlib

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology NNReal ENNReal BigOperators Convex
namespace SKValue

theorem parametric_spatial_error
    {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u : E} {v w : α → E} {l : Filter α} (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    (s : Set E := Set.univ) (seg : ∀ᶠ χ in l, [w χ -[ℝ] v χ] ⊆ s := by simp)
    {f : α → E → F} {f' : α → E → E →L[𝕜] F}
    (df' : ∀ᶠ p in l ×ˢ 𝓝[s] u, HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2)
    {φ : E →L[𝕜] F} (cf' : Tendsto ↿f' (l ×ˢ 𝓝[s] u) (𝓝 φ)) :
    (fun χ => f χ (v χ) - f χ (w χ) - φ (v χ - w χ)) =o[l] (fun χ => v χ - w χ) := by
  rw [isLittleO_iff]
  intro ε hε
  replace df' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], HasFDerivWithinAt (f χ) (f' χ z) s z :=
    df'.segment_of_prod_nhdsWithin hw hv seg
  replace cf' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], ‖f' χ z - φ‖ < ε := by
    simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at cf'
    exact (cf' ε hε).segment_of_prod_nhdsWithin hw hv seg
  filter_upwards [seg, df', cf'] with χ seg df' cf'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (df' z hz).mono seg) (fun z hz => (cf' z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

lemma hasDerivAt_parametric_comp {f fx : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {t a b : ℝ}
    (hd : HasDerivAt (fun s ↦ f s (φ t)) a t) (hφ : HasDerivAt φ b t)
    (hx : ∀ᶠ p : ℝ×ℝ in 𝓝 (t,φ t), HasDerivAt (f p.1) (fx p.1 p.2) p.2)
    (hc : ContinuousAt (fun p : ℝ×ℝ ↦ fx p.1 p.2) (t,φ t)) :
    HasDerivAt (fun s ↦ f s (φ s)) (a+fx t (φ t)*b) t := by
  have hsp := parametric_spatial_error hφ.continuousAt tendsto_const_nhds
    (s := Set.univ) (seg := by simp) (f := f) (f' := fun s x ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (fx s x))
    (φ := (1 : ℝ →L[ℝ] ℝ).smulRight (fx t (φ t)))
    (df' := by
      rw [nhdsWithin_univ,←nhds_prod_eq]
      exact hx.mono (fun p hp ↦ hp.hasFDerivAt.hasFDerivWithinAt))
    (cf' := by
      rw [nhdsWithin_univ,←nhds_prod_eq]
      exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.continuousAt.comp hc)
  have hsmall := (hsp.trans_isBigO hφ.isBigO_sub).add
    (hd.isLittleO.add (hφ.isLittleO.const_mul_left (fx t (φ t))))
  apply HasDerivAt.of_isLittleO
  have heq : (fun s ↦ f s (φ s)-f s (φ t)-
      (1 : ℝ →L[ℝ] ℝ).smulRight (fx t (φ t)) (φ s-φ t) +
      ((f s (φ t)-f t (φ t)-(s-t) • a)+fx t (φ t)*(φ s-φ t-(s-t) • b))) =
      (fun s ↦ f s (φ s)-f t (φ t)-(s-t) • (a+fx t (φ t)*b)) := by
    funext s
    simp only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,smul_eq_mul]
    ring
  rw [heq] at hsmall
  exact hsmall

end SKValue

end

end OAI
