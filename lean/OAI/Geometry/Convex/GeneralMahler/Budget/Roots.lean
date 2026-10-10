import Mathlib

namespace OAI
/-! Exterior square-root kernel integrals in §05. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Roots

def u (t:ℝ):= √(1+t)-√t
def p (t:ℝ):=u t^2
def xk (t:ℝ):=2*u t^4/(1+2*t)
def yk (t:ℝ):=(1/2:ℝ)*u t^2*(1/(1+t)+(1/2:ℝ)*(1-√t / √(1+t))^2)
lemma u_pos {t:ℝ} (h:0≤t) : 0<u t := by unfold u; apply sub_pos.mpr; apply Real.sqrt_lt_sqrt h; linarith
lemma u_add {t:ℝ} (h:0≤t) : u t*(√(1+t)+√t)=1 := by
  unfold u
  nlinarith [Real.sq_sqrt h,Real.sq_sqrt (show 0≤1+t by linarith)]
lemma sqrt_top {t:ℝ} (h:0≤t) : √(1+t)=(1+p t)/(2*u t) := by
  have he := u_pos h
  have hh := u_add h
  field_simp
  unfold p; unfold u at *; nlinarith
lemma sqrt_bot {t:ℝ} (h:0≤t) : √t=(1-p t)/(2*u t) := by
  have he := u_pos h; have hh:= u_add h; field_simp
  unfold p; unfold u at *; nlinarith
lemma t_p {t:ℝ} (h:0≤t) : t=(1-p t)^2/(4*p t) := by
  have hp : 0<p t := pow_pos (u_pos h) _
  have he := Real.sq_sqrt h
  rw [sqrt_bot h,div_pow] at he
  calc
    t = _ := he.symm
    _ = _ := by unfold p; ring
lemma p_lt {t:ℝ} (h:0<t) : p t<1 := by
  have he := sqrt_bot h.le
  have hv := Real.sqrt_pos.2 h
  have hu := u_pos h.le
  field_simp at he
  nlinarith
lemma dp {t:ℝ} (h:0<t) :
    HasDerivAt p (-(4*p t^2)/(1-p t^2)) t := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  have hu := u_pos h.le
  have hl := p_lt h
  have ht : 0 <1+t := by linarith
  have he : HasDerivAt u ((1/(2*√(1+t)))-(1/(2*√t))) t :=
    by
      convert ((((hasDerivAt_id' t).const_add 1).sqrt ht.ne').sub ((hasDerivAt_id' t).sqrt h.ne')) using 1
      all_goals rfl
  convert he.pow 2 using 1
  all_goals first | rfl | skip
  rw [sqrt_top h.le,sqrt_bot h.le]
  have hs : 1-p t^2≠0 := by nlinarith
  have hv : 1-p t≠0 := by linarith
  norm_num
  field_simp
  unfold p; ring

lemma x_formula {t:ℝ} (h:0<t) :
    xk t=4*p t^3/(1+p t^2) := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  unfold xk
  conv_lhs=> rhs; rw [t_p h.le]
  field_simp
  unfold p; ring
lemma y_formula {t:ℝ} (h:0<t) :
    yk t=(1/(1+p t) - p t/2)/2*(4*p t^2/(1-p t^2)) := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  have hu := u_pos h.le; have hx:= p_lt h
  have hz : 1-p t^2≠0 := by nlinarith
  unfold yk
  rw [sqrt_top h.le,sqrt_bot h.le]
  conv_lhs =>
    rhs; lhs; rhs; rw [t_p h.le]
  field_simp
  unfold p; ring

lemma pu_limit : Tendsto p atTop (𝓝 0) := by
  let g := fun t:ℝ=> √(1+t)+√t
  have ht : Tendsto g atTop atTop := by
    apply tendsto_atTop_mono (g:=g) _ Real.tendsto_sqrt_atTop
    intro x; change √x ≤ √(1+x)+√x; linarith [Real.sqrt_nonneg (1+x)]
  have he : Tendsto u atTop (𝓝 0) := by
    apply Tendsto.congr' _ (tendsto_inv_atTop_zero.comp ht)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t h
    have ha := u_pos h; have hh := u_add h
    have hs : g t≠0 := by
      unfold g; positivity
    change (g t)⁻¹=u t
    field_simp
    linarith
  have h := he.pow 2; norm_num at h; exact h
lemma cu : Continuous p := by unfold p u; fun_prop

def fx (t:ℝ) := -(Real.log (1+p t^2)-p t^2/2)
def fy (t:ℝ) := -(Real.log (1+p t)/2-p t^2/8)
lemma dfx {t:ℝ} (h:0<t) : HasDerivAt fx (xk t) t := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  have he := ((((((dp h).pow 2).const_add 1).log (by change 1+p t^2≠0; positivity)).sub
    (((dp h).pow 2).div_const 2))).neg
  convert he using 1
  all_goals first | rfl | skip
  rw [x_formula h]
  have hl:=p_lt h
  have hs : 1-p t^2≠0 := by nlinarith
  norm_num
  field_simp; ring
lemma dfy {t:ℝ} (h:0<t) : HasDerivAt fy (yk t) t := by
  have hp : 0<p t := pow_pos (u_pos h.le) _
  convert ((((((dp h).const_add 1).log (by positivity)).div_const 2).sub
    (((dp h).pow 2).div_const 8)).neg) using 1
  all_goals first | rfl | skip
  rw [y_formula h]; norm_num; ring
lemma area_template {f g:ℝ→ℝ} (hf:ContinuousAt f 0) (h:Tendsto f atTop (𝓝 0))
    (hp:∀ t,0<t→ 0≤g t) (hd:∀ t,0<t→HasDerivAt f (g t) t) :
    IntegrableOn g (Ioi 0) ∧ (∫ t in Ioi 0,g t)=-f 0 := by
  have he := integrableOn_Ioi_deriv_of_nonneg hf.continuousWithinAt hd hp h
  refine ⟨he,?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto hf.continuousWithinAt hd he h

lemma puc (f:ℝ→ℝ) (hf:ContinuousOn f (Ici 0)) :
    Continuous (fun x=>f (p x)) := hf.comp_continuous cu (fun x=> mem_Ici.mpr (show 0 ≤ p x from sq_nonneg _))
lemma x_area :
    IntegrableOn xk (Ioi 0) ∧ (∫ t in Ioi 0,xk t)=Real.log 2 -1/2 := by
  let f := fun x:ℝ=> -(Real.log (1+x^2)-x^2/2)
  have hf : Continuous f := by unfold f; fun_prop (disch:= first | (intro x; positivity) | positivity)
  have hp : Continuous fx := hf.comp cu
  have ht : Tendsto fx atTop (𝓝 0) := by
    have h:= (hf.tendsto 0).comp pu_limit
    change Tendsto fx atTop (𝓝 (f 0)) at h; norm_num [f] at h; exact h
  have hh := area_template hp.continuousAt ht (fun t h=> show 0≤ xk t by unfold xk; positivity)
    (fun t h=>dfx h)
  norm_num [fx,p,u] at hh ⊢
  exact hh

lemma y_area :
    IntegrableOn yk (Ioi 0) ∧ (∫ t in Ioi 0,yk t)=Real.log 2/2 -1/8 := by
  let f := fun x:ℝ=> -(Real.log (1+x)/2-x^2/8)
  have hf : ContinuousOn f (Ici 0) := by
    unfold f; fun_prop (disch:= first | (intro x hx; change 0≤x at hx; positivity) | positivity)
  have hp : Continuous fy := puc f hf
  have hC : ContinuousAt f 0 := by unfold f; fun_prop (disch:=norm_num)
  have ht : Tendsto fy atTop (𝓝 0)  := by
    have h := hC.tendsto.comp pu_limit
    change Tendsto fy atTop (𝓝 (f 0)) at h
    norm_num [f] at h; exact h
  have hh := area_template hp.continuousAt ht (fun t h=> show 0≤ yk t by unfold yk; positivity)
    (fun t h=>dfy h)
  norm_num [fy,p,u] at hh ⊢
  exact hh
end GeneralMahler.Roots

end

end OAI
