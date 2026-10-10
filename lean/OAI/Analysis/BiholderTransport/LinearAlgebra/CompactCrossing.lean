import Mathlib

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bilinear_lower_of_unit (L : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ}
    (h : ∀ v:E, ‖v‖=1 → c ≤ L v v) (v:E) : c*‖v‖^2 ≤ L v v := by
  by_cases hv : v=0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖=1 := by simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have he : v=‖v‖ • w := by dsimp [w]; rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have H := mul_le_mul_of_nonneg_left (h w hw) (sq_nonneg ‖v‖)
  calc
    c*‖v‖^2 = ‖v‖^2*c := mul_comm _ _
    _ ≤ ‖v‖^2*L w w := H
    _ = L (‖v‖ • w) (‖v‖ • w) := by simp only [map_smul,smul_apply,smul_eq_mul]; ring
    _ = L v v := by rw [←he]

lemma bilinear_diag_abs_le (L : E →L[ℝ] E →L[ℝ] ℝ) (v:E) :
    |L v v| ≤ ‖L‖*‖v‖^2 := by
  calc
    |L v v| = ‖L v v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖L v‖*‖v‖ := (L v).le_opNorm _
    _ ≤ (‖L‖*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)
    _ = ‖L‖*‖v‖^2 := by ring

lemma bilinear_time_hasDerivAt {H : ℝ×Q → E →L[ℝ] E →L[ℝ] ℝ}
    {t:ℝ} {q:Q} (hH : DifferentiableAt ℝ H (t,q)) (v:E) :
    HasDerivAt (fun s => H (s,q) v v) (fderiv ℝ H (t,q) (1,0) v v) t := by
  have hp : HasDerivAt (fun s : ℝ => (s,q)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t q)
  have HD : HasDerivAt (fun s : ℝ => H (s,q)) (fderiv ℝ H (t,q) (1,0)) t :=
    HasFDerivAt.comp_hasDerivAt (l := H) (l' := fderiv ℝ H (t,q))
      (f := fun s : ℝ => (s,q)) t hH.hasFDerivAt hp
  have HV := (HD.clm_apply (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t v)
  simpa only [Function.comp_def,map_zero,add_zero,zero_add] using HV
end WeakMTWTransport

end

end OAI
