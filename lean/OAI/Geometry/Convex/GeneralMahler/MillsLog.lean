import OAI.Geometry.Convex.GeneralMahler.Mills

namespace OAI
/-! Polynomial bounds and primitive integrations for log profiles. -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology NNReal ENNReal
namespace GeneralMahler

lemma poly_of_d {f g:ℝ→ℝ} (h:∀ x, HasDerivAt f (g x) x)
    (hg:PolyBound g) : PolyBound f := by
  obtain ⟨C,n,hC,hg⟩ := hg
  have HE (a b:ℝ) (hh:a<b) :
      ∃ t∈Ioo a b,f b - f a = g t*(b-a) := by
    have hi : Differentiable ℝ f := fun x=>(h x).differentiableAt
    obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope f hh hi.continuous.continuousOn hi.differentiableOn
    rw [(h t).deriv, eq_div_iff (sub_pos.mpr hh).ne'] at he
    exact ⟨t,ht,he.symm⟩
  have he (x:ℝ) : ‖f x-f 0‖ ≤ C*(1+‖x‖)^n*‖x‖ := by
    have hb (t:ℝ) (ht:‖t‖≤‖x‖) (hh:f x-f 0=g t*x) :
        ‖f x-f 0‖≤C*(1+‖x‖)^n*‖x‖ := by rw [hh,norm_mul]; gcongr; apply le_trans (hg t); gcongr
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · obtain ⟨t,ht,h⟩ := HE x 0 hx
      apply hb t
      · rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_neg hx,abs_of_neg ht.2]; linarith [ht.1]
      linarith
    · simp
    obtain ⟨t,ht,h⟩ := HE 0 x hx
    apply hb t
    · rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hx,abs_of_pos ht.1]; exact ht.2.le
    rwa [sub_zero] at h
  refine ⟨‖f 0‖+C,n+1,add_nonneg (by positivity) hC,fun x=>?_⟩
  have h₀ : ‖f x‖ ≤ ‖f x-f 0‖+‖f 0‖ := by simpa using norm_add_le (f x-f 0) (f 0)
  apply le_trans h₀
  rw [add_mul,pow_succ]
  have hp : (1:ℝ) ≤ (1+‖x‖)^n := one_le_pow₀ (by simp)
  have he' := he x
  have h₁ := mul_le_mul_of_nonneg_left (show 1≤(1+‖x‖)^n * (1+‖x‖) by nlinarith [norm_nonneg x]) (norm_nonneg (f 0))
  have h₂ : C*(1+‖x‖)^n*‖x‖ ≤ C*((1+‖x‖)^n * (1+‖x‖)) := by rw [← mul_assoc]; gcongr; simp
  linarith

namespace Layers
def LC (x:ℝ) := Real.log (MillsC x)
lemma d_lc (x:ℝ) : HasDerivAt LC (-MillsJ x) x := by
  convert (d_mc x).log (mc_pos x).ne' using 1
  all_goals first | rfl | (unfold MillsW; field_simp [ne_of_gt (mc_pos x)])
lemma c_lc : Continuous LC := continuous_iff_continuousAt.mpr fun x => (d_lc x).continuousAt
lemma poly_lc : PolyBound LC := poly_of_d d_lc poly_mj.neg
def LP (x:ℝ) := Real.log (p x)
lemma d_lp (x:ℝ) : HasDerivAt LP (MillsC x) x :=
  (d_p x).log (p_pos x).ne'
lemma c_lp : Continuous LP := continuous_iff_continuousAt.mpr fun x=> (d_lp x).continuousAt
lemma poly_lp : PolyBound LP := poly_of_d d_lp poly_mc

lemma int_lp : Integrable (fun x=>phi x*LP x) :=
  (rapid_phi.product poly_lp).integrable_real (c_phi.measurable.mul c_lp.measurable)
lemma int_lc : Integrable (fun x=>phi x*LC x) :=
  (rapid_phi.product poly_lc).integrable_real (c_phi.measurable.mul c_lc.measurable)

lemma logp_average : (∫ x,phi x*LP x)=-1 := by
  let f := fun x=>p x*LP x-p x
  have hd (x:ℝ) : HasDerivAt f (phi x*LP x) x := by
    convert ((d_p x).mul (d_lp x)).sub (d_p x) using 1
    all_goals first | rfl | (unfold MillsC; field_simp [ne_of_gt (p_pos x)]; ring)
  have ha : Tendsto f atBot (𝓝 0) := by
    have h := ((rapid_p.product poly_lp).tail_limit_bot).sub pbot
    rw [sub_zero] at h
    apply Tendsto.congr' _ h
    filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx; simp [f,st,not_le_of_gt hx]
  have hb : Tendsto f atTop (𝓝 (-1)) := by
    have h : Tendsto LP atTop (𝓝 0) := by have h := ptop.log one_ne_zero; rw [Real.log_one] at h; exact h
    simpa [f] using (ptop.mul h).sub ptop
  simpa using integral_of_hasDerivAt_of_tendsto hd int_lp ha hb

lemma lc_integral_equiv :
    (∫ x,phi x*LC x) = LC 0 + ∫ x,(p x-st x)*MillsJ x := by
  have h := rapid_p.product poly_mj
  have hm := (cp.measurable.sub measurable_st).mul c_mj.measurable
  have hi := h.integrable_real hm
  let f := fun x=>phi x*LC x-(p x-st x)*MillsJ x
  have hf : Integrable f := int_lc.sub hi
  have hc : Tendsto (fun x=>(p x-st x)*LC x) atBot (𝓝 0) :=
    (rapid_p.product poly_lc).tail_limit_bot
  have hd : Tendsto (fun x=>(p x-st x)*LC x) atTop (𝓝 0) :=
    (rapid_p.product poly_lc).tail_limit
  let F := fun x=>p x*LC x
  let G := fun x=>(p x-1)*LC x
  have hl : (∫ x in Iic 0,f x) = F 0 := by
    have hv : Tendsto F atBot (𝓝 0) := by
      apply Tendsto.congr' _ hc
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx; simp [st,not_le_of_gt hx,F]
    have hh := integral_Iic_of_hasDerivAt_of_tendsto
      ((cp.mul c_lc).continuousWithinAt (x:=0)) (a:=0) (f:=F) (f':=f) ?_ hf.integrableOn hv
    · simpa using hh
    intro x hx
    convert (d_p x).mul (d_lc x) using 1
    all_goals first | rfl | (simp [f,st,not_le_of_gt (mem_Iio.mp hx)]; ring)
  have hr : (∫ x in Ioi 0,f x) = -G 0 := by
    have hv : Tendsto G atTop (𝓝 0) := by
      apply Tendsto.congr' _ hd
      filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx; simp [st,hx,G]
    have hh := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a:=0) (f:=G) (f':=f) ?_ hf.integrableOn hv
    · simpa using hh
    intro x hx
    convert ((d_p x).sub_const 1).mul (d_lc x) using 1
    all_goals first | rfl | (simp [f,st,mem_Ici.mp hx]; ring)
  have He : (∫ x,f x)=LC 0 := by
    rw [← integral_add_compl measurableSet_Iic hf (s:=Iic (0:ℝ)),compl_Iic,hl,hr]
    unfold F G; ring
  unfold f at He
  rw [integral_sub int_lc hi] at He
  linarith
end Layers
end GeneralMahler

end

end OAI
