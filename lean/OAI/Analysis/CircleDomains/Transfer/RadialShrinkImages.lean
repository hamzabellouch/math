import OAI.Analysis.CircleDomains.Sobolev.SmoothRadialShrinkInverse

namespace OAI

/-! Exact disk images of the ambient radial shrinker. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

@[simp] lemma smoothRadialShrinkHomeomorph_apply {t a b : ℝ}
    (ht : 0<t) (ht1 : t≤1) (ha : 0<a) (hab : a<b) (z : ℂ) :
    smoothRadialShrinkHomeomorph ht ht1 ha hab z=radialShrink t a b z := rfl

lemma radialShrink_image_inner {t a b : ℝ} (ht : 0<t) (ha : 0<a) (hab : a<b) :
    radialShrink t a b '' closedBall 0 a=closedBall 0 (t*a) := by
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    have hn : ‖z‖≤a := mem_closedBall_zero_iff.mp hz
    rw [radialShrink_inner ha hab hn]
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hn ht.le
  · intro y hy
    have hn : ‖y‖≤t*a := mem_closedBall_zero_iff.mp hy
    have hz : ‖t⁻¹ • y‖≤a := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
      calc
        t⁻¹*‖y‖ ≤ t⁻¹*(t*a) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ht.le)
        _ = a := by field_simp
    refine ⟨t⁻¹ • y,mem_closedBall_zero_iff.mpr hz,?_⟩
    rw [radialShrink_inner ha hab hz,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]

end CircleDomainRigidity

end

end OAI
