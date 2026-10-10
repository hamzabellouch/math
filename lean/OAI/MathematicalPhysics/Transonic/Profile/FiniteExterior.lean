import OAI.MathematicalPhysics.Transonic.Profile.ExteriorTail

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set SourceFamily AxisBarriers PhysicalExterior
open scoped ContDiff

lemma PhysicalWidth.local_above {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y∈Ioc M.radius W.endpoint) : 1<M.localProfile (y/M.radius) := by
  have hz : 1<y/M.radius := (lt_div_iff₀ M.radius_bounds.1).mpr (by simpa only [one_mul] using hy.1)
  have hb := W.rescale_full ⟨M.radius_bounds.1.le.trans hy.1.le,hy.2⟩
  have he := (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2.trans hz
  rw [(M.local_eventually_germ he).eq_of_nhds]
  exact M.sonic.germArc_above M.parameter ⟨hz,hb.2⟩

lemma PhysicalWidth.exterior_den_ne {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y∈Ioc M.radius W.endpoint) : profileDenom ell y (M.velocity y)≠0 := by
  have hyp : 0<y := M.radius_bounds.1.trans hy.1
  have hym : y∈Icc (0:ℝ) W.endpoint := ⟨hyp.le,hy.2⟩
  have he : M.radius*(y/M.radius)=y := mul_div_cancel₀ _ (ne_of_gt M.radius_bounds.1)
  have hf := sonic_exit_factors (r:=M.radius) (z:=y/M.radius) (p:=M.localProfile (y/M.radius))
    (by rw [he];exact W.y_abs hym) (W.U_abs hym) (W.local_above hy)
  rw [he] at hf
  change (1-Real.sqrt ell*y+(Real.sqrt ell-y)*M.velocity y<0) ∧
    (0<1+Real.sqrt ell*y-(y+Real.sqrt ell)*M.velocity y) at hf
  have hq : 1<Real.sqrt ell := by
    change 1<Real.sqrt (5/3)
    have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
    nlinarith only [hsq,Real.sqrt_nonneg (5/3:ℝ)]
  have hv := abs_lt.mp (W.velocity_abs hym)
  have hn := denominator_neg hq hyp hv hf.1 hf.2 le_rfl ⟨hv.1.le,le_rfl⟩
  rw [Real.sq_sqrt (by norm_num [ell] : (0:ℝ)≤ell)] at hn
  exact ne_of_lt hn

lemma PhysicalWidth.exterior_derivative {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y∈Ioc M.radius W.endpoint) :
    HasDerivAt M.velocity (field ell M.beta (y,M.velocity y)) y := by
  have hym : y∈Icc (0:ℝ) W.endpoint := ⟨M.radius_bounds.1.le.trans hy.1.le,hy.2⟩
  have hd := ((W.velocity_smooth hym).differentiableAt (by norm_num)).hasDerivAt
  apply hd.congr_deriv
  apply (eq_div_iff (W.exterior_den_ne hy)).mpr
  exact (mul_comm _ _).trans (W.velocity_equation hym)

end SepticProfile.SonicShooting

end
end

end OAI
