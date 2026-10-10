import OAI.Probability.SLE.Loewner.UnivalentKoebeTransform
import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! Integrating the exact logarithmic-derivative inequality gives the
sharp radial derivative majorant. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology

namespace SLEExactGauge

lemma disk_logarithmic_derivative_re_bound {f : ℂ → ℂ}
    (hpre : ∀ a : ℂ, ‖a‖<1 →
      ‖((1-‖a‖^2:ℝ):ℂ)*deriv (deriv f) a/deriv f a-2*star a‖≤4)
    (u : ℂ) (hu : ‖u‖=1) (t : ℝ) (ht : t∈Ico 0 1) :
    (u*deriv (deriv f) ((t:ℂ)*u)/deriv f ((t:ℂ)*u)).re≤
      3/(1-t)+1/(1+t) := by
  have ha : ‖(t:ℂ)*u‖=t := by simp [hu,abs_of_nonneg ht.1]
  have hd : 0<1-t^2 := by nlinarith [ht.1,ht.2]
  have hunit : star u*u=1 := by
    rw [Complex.star_def,Complex.conj_mul',hu]
    norm_num
  have hstarcast : star (t:ℂ)=(t:ℂ) := by apply Complex.ext <;> simp
  have he :
      (((1-t^2:ℝ):ℂ)*deriv (deriv f) ((t:ℂ)*u)/deriv f ((t:ℂ)*u)-2*star ((t:ℂ)*u))*u =
      ((1-t^2:ℝ):ℂ)*(u*deriv (deriv f) ((t:ℂ)*u)/deriv f ((t:ℂ)*u))-((2*t:ℝ):ℂ) := by
    calc
      _ = ((1-t^2:ℝ):ℂ)*(u*deriv (deriv f) ((t:ℂ)*u)/deriv f ((t:ℂ)*u))-
          2*(t:ℂ)*(star u*u) := by simp only [star_mul,hstarcast]; ring
      _ = _ := by rw [hunit]; push_cast; ring
  have hn := hpre ((t:ℂ)*u) (by rw [ha]; exact ht.2)
  rw [ha] at hn
  have hRe := (Complex.re_le_norm _).trans (show
      ‖((((1-t^2:ℝ):ℂ)*deriv (deriv f) ((t:ℂ)*u)/deriv f ((t:ℂ)*u)-2*star ((t:ℂ)*u))*u)‖≤4 by
    rw [norm_mul,hu,mul_one]; exact hn)
  rw [he] at hRe
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hRe
  have hb : (u*deriv (deriv f) ((t:ℂ)*u)/deriv f ((t:ℂ)*u)).re≤(4+2*t)/(1-t^2) :=
    (le_div_iff₀ hd).mpr (by linarith)
  have heq : (4+2*t)/(1-t^2)=3/(1-t)+1/(1+t) := by
    have h1 : 1-t≠0 := by linarith [ht.2]
    have h2 : 1+t≠0 := by linarith [ht.1]
    field_simp
    ring
  exact hb.trans_eq heq

lemma univalent_radial_derivative_bound {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hpre : ∀ a : ℂ, ‖a‖<1 →
      ‖((1-‖a‖^2:ℝ):ℂ)*deriv (deriv f) a/deriv f a-2*star a‖≤4)
    (u : ℂ) (hu : ‖u‖=1) (r : ℝ) (hr : r∈Ico 0 1) :
    ‖deriv f ((r:ℂ)*u)‖≤‖deriv f 0‖*(1+r)/(1-r)^3 := by
  let y (t : ℝ) := deriv f ((t:ℂ)*u)
  let c (t : ℝ) := u*deriv (deriv f) ((t:ℂ)*u)/y t
  let q (t : ℝ) := 3/(1-t)+1/(1+t)
  let Q (t : ℝ) := Real.log (1+t)-3*Real.log (1-t)
  have hat (t : ℝ) (ht : t∈Icc 0 r) : (t:ℂ)*u∈ball 0 1 := by
    rw [mem_ball_zero_iff,norm_mul,hu,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact ht.2.trans_lt hr.2
  have hyt (t : ℝ) (ht : t∈Icc 0 r) : y t≠0 :=
    univalent_deriv_ne_zero isOpen_ball hf hi (hat t ht)
  have hyd (t : ℝ) (ht : t∈Icc 0 r) :
      HasDerivAt y (u*deriv (deriv f) ((t:ℂ)*u)) t := by
    have ha := (hf.analyticAt (isOpen_ball.mem_nhds (hat t ht))).deriv
    have hd := (ha.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const u)
    simpa only [ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul,Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul,Function.comp_def,y] using hd
  have hyc : ContinuousOn y (Icc 0 r) := fun t ht => (hyd t ht).continuousAt.continuousWithinAt
  have hcc : ContinuousOn c (Icc 0 r) := by
    apply ContinuousOn.div ?_ hyc hyt
    apply continuousOn_const.mul
    intro t ht
    have houter : ContinuousAt (deriv (deriv f)) ((t:ℂ)*u) :=
      (hf.analyticAt (isOpen_ball.mem_nhds (hat t ht))).deriv.deriv.continuousAt
    exact (ContinuousAt.comp (g := deriv (deriv f)) (f := fun s : ℝ => (s:ℂ)*u)
      houter (by fun_prop)).continuousWithinAt
  have hyode (t : ℝ) (ht : t∈Icc 0 r) : HasDerivWithinAt y (c t*y t) (Icc 0 r) t := by
    have he : c t*y t=u*deriv (deriv f) ((t:ℂ)*u) := by dsimp only [c]; field_simp [hyt t ht]
    rw [he]
    exact (hyd t ht).hasDerivWithinAt
  have hformula := complex_linear_ode_exp r hr.1 y c hcc hyode
  have hqc : ContinuousOn q (Icc 0 r) := by
    apply ContinuousOn.add
    · exact continuousOn_const.div (by fun_prop) (fun t ht => by linarith [ht.2,hr.2])
    · exact continuousOn_const.div (by fun_prop) (fun t ht => by linarith [ht.1])
  have hQ (t : ℝ) (ht : t∈Icc 0 r) : HasDerivAt Q (q t) t := by
    have hp : 1+t≠0 := by linarith [ht.1]
    have hm : 1-t≠0 := by linarith [ht.2,hr.2]
    have h := (((hasDerivAt_id t).const_add 1).log hp).sub
      ((((hasDerivAt_id t).const_sub 1).log hm).const_mul 3)
    change HasDerivAt Q _ t at h
    convert h using 1
    dsimp [q]
    ring
  have hQI : ∫ t in (0:ℝ)..r, q t=Q r := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := r)
      (fun t ht => hQ t (by simpa only [uIcc_of_le hr.1] using ht)) (hqc.intervalIntegrable_of_Icc hr.1)
    simpa [Q] using h
  have hbound : (∫ t in (0:ℝ)..r, c t).re≤Q r := by
    have hre : (∫ t in (0:ℝ)..r, c t).re=∫ t in (0:ℝ)..r, (c t).re :=
      (Complex.reCLM.intervalIntegral_comp_comm (hcc.intervalIntegrable_of_Icc hr.1)).symm
    rw [←hQI,hre]
    apply intervalIntegral.integral_mono_on hr.1
      ((Complex.continuous_re.comp_continuousOn hcc).intervalIntegrable_of_Icc hr.1) (hqc.intervalIntegrable_of_Icc hr.1)
    intro t ht
    exact disk_logarithmic_derivative_re_bound hpre u hu t ⟨ht.1,ht.2.trans_lt hr.2⟩
  have hexp : Real.exp (Q r)=(1+r)/(1-r)^3 := by
    have hp : 0<1+r := by linarith [hr.1]
    have hm : 0<1-r := by linarith [hr.2]
    dsimp [Q]
    rw [Real.exp_sub,Real.exp_log hp,show 3*Real.log (1-r)=(3:ℕ)*Real.log (1-r) by norm_num,
      Real.exp_nat_mul,Real.exp_log hm]
  calc
    ‖deriv f ((r:ℂ)*u)‖ = ‖y 0‖*Real.exp ((∫ t in (0:ℝ)..r, c t).re) := by
      change ‖y r‖=_
      rw [hformula,norm_mul,Complex.norm_exp]
    _ ≤ ‖y 0‖*Real.exp (Q r) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbound) (norm_nonneg _)
    _ = ‖deriv f 0‖*(1+r)/(1-r)^3 := by simp only [y,Complex.ofReal_zero,zero_mul]; rw [hexp]; ring

end SLEExactGauge

end

end OAI
