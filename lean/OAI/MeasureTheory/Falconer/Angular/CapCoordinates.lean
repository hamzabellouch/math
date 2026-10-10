import OAI.MeasureTheory.Falconer.Geometry.ChartFrame

namespace OAI

/-!
# Small sphere caps have small gnomonic coordinates

This estimate converts the geometric cap support of an angular partition
into the compact coordinate support required by nonstationary integration.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem small_cap_chart_displacement {w h : E} (hw : ‖w‖ = 1)
    (horth : inner ℝ w h = 0) {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hcap : ‖‖w+h‖⁻¹ • (w+h)-w‖ ≤ δ) : ‖h‖ ≤ 2*δ := by
  have hne := tangent_chart_nonzero hw horth
  have hr : 0 < ‖w+h‖ := norm_pos_iff.mpr hne
  have he : perpendicularPart w (‖w+h‖⁻¹ • (w+h)-w) = ‖w+h‖⁻¹ • h := by
    simp only [perpendicularPart,inner_sub_right,real_inner_smul_right,inner_add_right,
      real_inner_self_eq_norm_sq,hw,one_pow,horth,add_zero,mul_one]
    module
  have hp := (norm_perpendicularPart_le hw (‖w+h‖⁻¹ • (w+h)-w)).trans hcap
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)] at hp
  have hh : ‖h‖ ≤ ‖w+h‖*δ := by
    have hh := mul_le_mul_of_nonneg_left hp hr.le
    rwa [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] at hh
  have ht : ‖w+h‖ ≤ 1+‖h‖ := by simpa only [hw] using norm_add_le w h
  have hbound := hh.trans (mul_le_mul_of_nonneg_right ht hδ)
  have hm : δ*‖h‖ ≤ (1/2 : ℝ)*‖h‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg h)
  nlinarith

end Falconer

end OAI
