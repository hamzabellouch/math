import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedControl

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace SevenEighths.CenteredMomentPlainGlobalBound
open HeckeFamily HeckeDyadic

 theorem weighted_central (χ:Character)(W:ℝ→ℂ)(D freq C K T:ℝ)
    (hD:0<D)(hC:0≤C)(hK:0≤K)(hT:0≤T)
    (hm:∀t:ℝ,(1+|t|)^4*‖mellin W (((1/2:ℝ):ℂ)+t*I)‖≤C)
    (hs:∀t∈Icc (-T) T,‖series χ false (((1/2:ℝ):ℂ)+t*I+shift 0 freq)‖≤K*(1+|t|)^2):
    ‖∫t:ℝ in -T..T,integrand χ false W D 0 freq (((1/2:ℝ):ℂ)+t*I)‖≤C*K*Real.pi:=by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint:=integrable_inv_one_add_sq.const_mul (C*K)
  calc
    _≤∫t:ℝ in Ioc (-T) T,(C*K)*(1+t^2)⁻¹:=by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ false W D 0 freq hD]
      have hm':(1+|t|)^2*(‖mellin W (((1/2:ℝ):ℂ)+t*I)‖*(1+|t|)^2)≤C:=by
        nlinarith only [hm t]
      have hb:=CubicReflectionKernel.weighted_two_to_cauchy
        (mul_nonneg (norm_nonneg _) (sq_nonneg _)) t hm'
      have hh:=mul_le_mul_of_nonneg_left (hs t ⟨ht.1.le,ht.2⟩)
        (norm_nonneg (mellin W (((1/2:ℝ):ℂ)+t*I)))
      have hbK:=mul_le_mul_of_nonneg_right hb hK
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,zero_mul,
        sub_self,add_zero]
      norm_num only [add_zero,sub_self,Real.rpow_zero,mul_one]
      apply hh.trans
      convert hbK using 1 <;> ring
    _≤∫t:ℝ,(C*K)*(1+t^2)⁻¹:=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _=_:=by rw [integral_const_mul,integral_univ_inv_one_add_sq]

 theorem finite_strip_bound (χ:Character)(hχ:χ.residue≠1)(W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hWs:Function.support W⊆Icc a b)(hW:ContDiff ℝ ∞ W)
    (D freq C K:ℝ)(hD:1≤D)(hC:0≤C)(hK:0≤K)
    (hm:∀x∈Icc (1/2:ℝ) 2,∀t:ℝ,(1+|t|)^6*‖mellin W ((x:ℂ)+t*I)‖≤C)
    (hs:∀x∈Icc (1/2:ℝ) 2,∀t:ℝ,
      ‖series χ false ((x:ℂ)+t*I+shift 0 freq)‖≤K*(1+|t|)^2):
    ‖polynomial χ false W D 0 freq‖≤(1/(2*Real.pi))*
      (C*K*Real.pi+3*C*K+C*HeckeReciprocalBound.bound 2*Real.pi):=by
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hm4 (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(t:ℝ):
      (1+|t|)^4*‖mellin W ((x:ℂ)+t*I)‖≤C:=by
    apply le_trans _ (hm x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · norm_num
  have hcent:=weighted_central χ W D freq C K D hD0 hC hK hD0.le
    (hm4 _ (by norm_num)) (fun t _=>hs _ (by norm_num) t)
  have hg (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(y:ℝ)(hy:|y|=D):
      ‖series χ false ((x:ℂ)+y*I+shift 0 freq)‖≤K*(1+D)^2:=by
    simpa only [hy] using hs x hx y
  have hlo:=horizontal_join_bound χ false W D 0 freq (1/2) 2 (-D) C (K*(1+D)^2) 4
    hD (by norm_num) hC (by positivity) (fun x hx=>hm4 x hx (-D))
    (fun x hx=>hg x hx (-D) (by simp [abs_of_nonneg hD0.le]))
  have hhi:=horizontal_join_bound χ false W D 0 freq (1/2) 2 D C (K*(1+D)^2) 4
    hD (by norm_num) hC (by positivity) (fun x hx=>hm4 x hx D)
    (fun x hx=>hg x hx D (abs_of_nonneg hD0.le))
  have htail:=absolute_tail_bound χ false W D 2 0 freq C D 4 hD0 (by norm_num) hC hD0.le
    (hm _ (by norm_num))
  have hpower:D^(3/2:ℝ)≤(1+D)^2:=by
    have hp:D^(3/2:ℝ)≤D^(2:ℝ):=Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
    rw [Real.rpow_two] at hp
    nlinarith
  have hratio:D^(3/2:ℝ)/(1+D)^2≤1:=(div_le_one (by positivity)).mpr hpower
  have hratio4:D^(3/2:ℝ)/(1+D)^4≤1:=by
    apply (div_le_one (by positivity)).mpr
    apply hpower.trans
    exact pow_le_pow_right₀ (by linarith : 1≤1+D) (by norm_num : 2≤4)
  have hj:(C*D^(3/2:ℝ)*(K*(1+D)^2)/(1+D)^4)*(3/2)≤(3/2)*C*K:=by
    have he:(C*D^(3/2:ℝ)*(K*(1+D)^2)/(1+D)^4)*(3/2)=
        ((3/2)*C*K)*(D^(3/2:ℝ)/(1+D)^2):=by field_simp
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hratio
  have ht:(C*D^(3/2:ℝ)*HeckeReciprocalBound.bound 2)/(1+D)^4*Real.pi≤
      C*HeckeReciprocalBound.bound 2*Real.pi:=by
    have hb:0≤HeckeReciprocalBound.bound 2:=tsum_nonneg (fun _=>norm_nonneg _)
    have he:(C*D^(3/2:ℝ)*HeckeReciprocalBound.bound 2)/(1+D)^4*Real.pi=
        (C*HeckeReciprocalBound.bound 2*Real.pi)*(D^(3/2:ℝ)/(1+D)^4):=by ring
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hratio4
  norm_num only [add_zero,show (2:ℝ)-1/2=3/2 by norm_num,show |(2:ℝ)-1/2|=3/2 by norm_num,
    abs_neg,abs_of_nonneg hD0.le] at hlo hhi htail
  rw [polynomial_finite_shift χ hχ false W a b ha hWs hW D 0 freq (1/2) 2 D hD0
    (by norm_num) hD0.le (by intro s hs h; cases h),norm_mul]
  have hnorm:‖(1/(2*Real.pi):ℂ)‖=(1/(2*Real.pi):ℝ):=by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left ((norm_four_sides _ _ _ _).trans ?_) (by positivity)
  simp only [ofReal_neg] at hlo
  linarith [hlo.trans hj,hhi.trans hj,htail.trans ht]

end SevenEighths.CenteredMomentPlainGlobalBound

end

end OAI
