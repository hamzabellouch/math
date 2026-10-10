import OAI.Analysis.PlaneSpectrum.Fourier
import OAI.Geometry.PlaneColoring.Coloring

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma oscillatory_integral_bound {a b : ℝ} (hab : a ≤ b)
    {g g' : ℝ → ℂ} {w w' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (hgi : IntervalIntegrable g' volume a b) (hwi : IntervalIntegrable w' volume a b)
    (hn : ∀ t ∈ Icc a b, ‖g t‖=1) (hwpos : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hwneg : ∀ t ∈ Icc a b, w' t ≤ 0)
    (he : ∀ t ∈ Icc a b, ((w t : ℂ)*Complex.I)*g' t=g t) :
    ‖∫ t in a..b, g t‖ ≤ 2*w a := by
  have hwu : ∀ t ∈ uIcc a b, HasDerivAt (fun t => (w t : ℂ)*Complex.I) ((w' t : ℂ)*Complex.I) t := by
    intro t ht
    exact ((hw t (by simpa [uIcc_of_le hab] using ht)).ofReal_comp).mul_const _
  have hs := intervalIntegral.integral_mul_deriv_eq_deriv_mul hwu
    (fun t ht => hg t (by simpa [uIcc_of_le hab] using ht)) ((show IntervalIntegrable (fun t => (w' t : ℂ)) volume a b from
      ⟨Complex.ofRealCLM.integrable_comp hwi.1,Complex.ofRealCLM.integrable_comp hwi.2⟩).mul_const _) hgi
  have hleft : (∫ t in a..b, ((w t : ℂ)*Complex.I)*g' t) = ∫ t in a..b, g t :=
    intervalIntegral.integral_congr (fun t ht => he t (by simpa [uIcc_of_le hab] using ht))
  rw [hleft] at hs
  have hint : ‖∫ t in a..b, (w' t : ℂ)*Complex.I*g t‖ ≤ ∫ t in a..b, -w' t := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ hwi.neg
    filter_upwards with t ht
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,hn t ⟨ht.1.le,ht.2⟩,mul_one,mul_one,
      abs_of_nonpos (hwneg t ⟨ht.1.le,ht.2⟩)]
    rfl
  have hiw : (∫ t in a..b, -w' t)=w a-w b := by
    rw [intervalIntegral.integral_neg,intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hw t (by simpa [uIcc_of_le hab] using ht)) hwi]
    ring
  have hna : ‖(w a : ℂ)*Complex.I*g a‖=w a := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwpos a ⟨le_rfl,hab⟩),
      Complex.norm_I,hn a ⟨le_rfl,hab⟩,mul_one,mul_one]
  have hnb : ‖(w b : ℂ)*Complex.I*g b‖=w b := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwpos b ⟨hab,le_rfl⟩),
      Complex.norm_I,hn b ⟨hab,le_rfl⟩,mul_one,mul_one]
  rw [hs]
  have hh := norm_sub_le ((w b : ℂ)*Complex.I*g b-(w a : ℂ)*Complex.I*g a)
    (∫ t in a..b, (w' t : ℂ)*Complex.I*g t)
  have hh' := norm_sub_le ((w b : ℂ)*Complex.I*g b) ((w a : ℂ)*Complex.I*g a)
  rw [hna,hnb] at hh'
  rw [hiw] at hint
  linarith
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
def circleOscillation (r t : ℝ) : ℂ := Complex.exp ((r*Real.cos t : ℝ)*Complex.I)
lemma circleOscillation_norm (r t : ℝ) : ‖circleOscillation r t‖=1 := Complex.norm_exp_ofReal_mul_I _
lemma circleOscillation_continuous (r : ℝ) : Continuous (circleOscillation r) := by unfold circleOscillation; fun_prop
lemma circleOscillation_hasDeriv (r t : ℝ) :
    HasDerivAt (circleOscillation r) ((-r*Real.sin t : ℝ)*Complex.I*circleOscillation r t) t := by
  unfold circleOscillation
  convert (((Real.hasDerivAt_cos t).const_mul r).ofReal_comp.mul_const Complex.I).cexp using 1
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  ring
lemma circleOscillation_tail {r a : ℝ} (hr : 0<r) (ha : 0<a) (hab : a≤Real.pi/2) :
    ‖∫ t in a..Real.pi/2, circleOscillation r t‖ ≤ 2/(r*Real.sin a) := by
  have hsin (t : ℝ) (ht : t ∈ Icc a (Real.pi/2)) : 0<Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi (ha.trans_le ht.1) (by linarith [ht.2,Real.pi_pos])
  have hcos (t : ℝ) (ht : t ∈ Icc a (Real.pi/2)) : 0≤Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
  let w := fun t => 1/(r*Real.sin t)
  let w' := fun t => -Real.cos t/(r*(Real.sin t)^2)
  have hw : ∀ t ∈ Icc a (Real.pi/2), HasDerivAt w (w' t) t := by
    intro t ht
    convert ((Real.hasDerivAt_sin t).const_mul r).inv (mul_ne_zero hr.ne' (hsin t ht).ne') using 1 <;> first
    | rfl
    | (change w = (fun y => r * Real.sin y)⁻¹; funext s; simp only [w,Pi.inv_apply,one_div])
    | (change -Real.cos t/(r*(Real.sin t)^2) = -(r*Real.cos t)/(r*Real.sin t)^2; field_simp)
  have hwi : IntervalIntegrable w' volume a (Real.pi/2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (Real.continuous_cos.neg.continuousOn) (continuous_const.mul (Real.continuous_sin.pow 2)).continuousOn
    intro t ht
    have ht' : t ∈ Icc a (Real.pi/2) := by simpa [uIcc_of_le hab] using ht
    exact mul_ne_zero hr.ne' (pow_ne_zero _ (hsin t ht').ne')
  have hi : IntervalIntegrable (fun t => (-r*Real.sin t : ℝ)*Complex.I*circleOscillation r t) volume a (Real.pi/2) := by
    apply Continuous.intervalIntegrable
    unfold circleOscillation
    fun_prop
  have h := oscillatory_integral_bound hab (fun t _ => circleOscillation_hasDeriv r t) hw hi hwi
    (fun t _ => circleOscillation_norm r t) (fun t ht => (one_div_pos.mpr (mul_pos hr (hsin t ht))).le)
    (fun t ht => by dsimp [w']; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hcos t ht)) (by positivity))
    (fun t ht => by
      dsimp [w]
      have hrC : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have hsC : (Real.sin t : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hsin t ht).ne'
      simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_neg]
      field_simp
      simp only [Complex.I_sq]
      ring)
  simpa only [w,mul_one_div] using h
lemma circleOscillation_quarter {r : ℝ} (hr : 1≤r) :
    ‖∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t‖ ≤ (1+Real.pi)/Real.sqrt r := by
  have hr0 : 0<r := lt_of_lt_of_le zero_lt_one hr
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs1 : 1≤Real.sqrt r := by simpa using Real.sqrt_le_sqrt hr
  let a := 1/Real.sqrt r
  have ha : 0<a := one_div_pos.mpr hs
  have ha1 : a≤1 := (div_le_one hs).mpr hs1
  have hab : a≤Real.pi/2 := by linarith [Real.pi_gt_three]
  have hi := circleOscillation_continuous r
  have hhead : ‖∫ t in (0:ℝ)..a, circleOscillation r t‖ ≤ a := by
    simpa [abs_of_nonneg ha.le] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := a) (C := (1:ℝ)) (fun t _ => (circleOscillation_norm r t).le)
  have htail := circleOscillation_tail hr0 ha hab
  have hsin := Real.mul_le_sin ha.le hab
  have hden : 0<r*(2/Real.pi*a) := by positivity
  have hh : 2/(r*Real.sin a) ≤ Real.pi/Real.sqrt r := by
    calc
      _ ≤ 2/(r*(2/Real.pi*a)) := div_le_div_of_nonneg_left (by norm_num) hden
        (mul_le_mul_of_nonneg_left hsin hr0.le)
      _ = Real.pi/Real.sqrt r := by
        dsimp [a]
        field_simp
        nlinarith [Real.sq_sqrt hr0.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := a))
    (hi.intervalIntegrable (a := a) (b := Real.pi/2))]
  have hn := norm_add_le (∫ t in (0:ℝ)..a, circleOscillation r t)
    (∫ t in a..Real.pi/2, circleOscillation r t)
  have hea : a + Real.pi/Real.sqrt r = (1+Real.pi)/Real.sqrt r := by dsimp [a]; ring
  linarith
lemma circleOscillation_pi_sub (r t : ℝ) :
    circleOscillation r (Real.pi-t) = (starRingEnd ℂ) (circleOscillation r t) := by
  simp only [circleOscillation,Real.cos_pi_sub,← Complex.exp_conj,map_mul,
    Complex.conj_ofReal,Complex.conj_I]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  ring
lemma circleOscillation_two_pi_sub (r t : ℝ) :
    circleOscillation r (2*Real.pi-t) = circleOscillation r t := by
  simp only [circleOscillation,Real.cos_two_pi_sub]
lemma circleOscillation_full {r : ℝ} (hr : 1≤r) :
    ‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation r t‖ ≤ 4*(1+Real.pi)/Real.sqrt r := by
  have hi := circleOscillation_continuous r
  have hq : (∫ t in Real.pi/2..Real.pi, circleOscillation r t) =
      (starRingEnd ℂ) (∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t) := by
    calc
      _ = ∫ t in (0:ℝ)..Real.pi/2, circleOscillation r (Real.pi-t) := by
        rw [intervalIntegral.integral_comp_sub_left]; congr 2 <;> ring
      _ = _ := by simp only [circleOscillation_pi_sub,intervalIntegral.intervalIntegral_conj]
  have hhalf : ‖∫ t in (0:ℝ)..Real.pi, circleOscillation r t‖ ≤
      2*((1+Real.pi)/Real.sqrt r) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := Real.pi/2))
      (hi.intervalIntegrable (a := Real.pi/2) (b := Real.pi)),hq]
    have hn := norm_add_le (∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t)
      ((starRingEnd ℂ) (∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t))
    rw [Complex.norm_conj] at hn
    linarith [circleOscillation_quarter hr]
  have hs : (∫ t in Real.pi..2*Real.pi, circleOscillation r t) =
      ∫ t in (0:ℝ)..Real.pi, circleOscillation r t := by
    calc
      _ = ∫ t in (0:ℝ)..Real.pi, circleOscillation r (2*Real.pi-t) := by
        rw [intervalIntegral.integral_comp_sub_left]; congr 2 <;> ring
      _ = _ := by simp only [circleOscillation_two_pi_sub]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := Real.pi))
    (hi.intervalIntegrable (a := Real.pi) (b := 2*Real.pi)),hs]
  have hn := norm_add_le (∫ t in (0:ℝ)..Real.pi, circleOscillation r t)
    (∫ t in (0:ℝ)..Real.pi, circleOscillation r t)
  rw [mul_div_assoc]
  linarith
end EuclideanFiveColor

end

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
def circleSymbol (ξ : ℂ) : ℂ := ∫ t, planePhase (direction t) ξ ∂angularMeasure
lemma circleSymbol_norm_le_one (ξ : ℂ) : ‖circleSymbol ξ‖≤1 := by
  simpa only [circleSymbol,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (Eventually.of_forall fun t => (planePhase_norm (direction t) ξ).le :
        ∀ᵐ t ∂angularMeasure, ‖planePhase (direction t) ξ‖ ≤ 1)
lemma circlePhase_real (ξ : ℂ) (t : ℝ) :
    planePhase (direction (t:Angles)) ξ = circleOscillation (2*Real.pi*‖ξ‖) (t-Complex.arg ξ) := by
  have hinner : inner ℝ (direction (t:Angles)) ξ = ‖ξ‖*Real.cos (t-Complex.arg ξ) := by
    rw [Complex.inner,direction_real,Circle.coe_exp,Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im]
    rw [Real.cos_sub]
    have hr := Complex.norm_mul_cos_arg ξ
    have hi := Complex.norm_mul_sin_arg ξ
    rw [← hr,← hi]
    ring
  rw [planePhase,hinner,Real.fourierChar_apply]
  simp only [circleOscillation]
  congr 1
  push_cast
  ring
lemma circleSymbol_integral (ξ : ℂ) :
    circleSymbol ξ = (2*Real.pi)⁻¹ • ∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t := by
  have hp : Function.Periodic (circleOscillation (2*Real.pi*‖ξ‖)) (2*Real.pi) := by
    intro t
    simp only [circleOscillation,Real.cos_add_two_pi]
  rw [circleSymbol,angularMeasure,AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2*Real.pi) 0]
  congr 1
  simp_rw [circlePhase_real]
  rw [intervalIntegral.integral_comp_sub_right]
  simpa [sub_eq_add_neg,add_comm] using hp.intervalIntegral_add_eq (-(Complex.arg ξ)) 0
lemma circleSymbol_sq_bound (ξ : ℂ) : ‖circleSymbol ξ‖^2 ≤ 400/(1+‖ξ‖) := by
  have hn : 0≤‖ξ‖ := norm_nonneg _
  by_cases hs : ‖ξ‖≤1
  · have hb := circleSymbol_norm_le_one ξ
    apply (le_div_iff₀ (by positivity : 0<1+‖ξ‖)).mpr
    nlinarith [norm_nonneg (circleSymbol ξ)]
  have hr : 1≤2*Real.pi*‖ξ‖ := by nlinarith [Real.pi_gt_three]
  have hb := circleOscillation_full hr
  rw [circleSymbol_integral,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity))]
  have hsqr := Real.sq_sqrt (by positivity : 0≤2*Real.pi*‖ξ‖)
  have hsqrt : 0<Real.sqrt (2*Real.pi*‖ξ‖) := Real.sqrt_pos.mpr (by positivity)
  have hlow : 0<2*Real.pi := by positivity
  have hq := (le_div_iff₀ hsqrt).mp hb
  have hpos := norm_nonneg (∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t)
  have hq2 : (‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖ * Real.sqrt (2*Real.pi*‖ξ‖))^2 ≤ (4*(1+Real.pi))^2 :=
    pow_le_pow_left₀ (mul_nonneg hpos hsqrt.le) hq 2
  apply (le_div_iff₀ (by positivity : 0<1+‖ξ‖)).mpr
  rw [mul_pow,hsqr] at hq2
  have hpi : Real.pi<4 := Real.pi_lt_four
  have hN : ‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖^2 * ‖ξ‖ ≤ 100 := by
    have hmul := mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le)
      (mul_nonneg (sq_nonneg (‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖)) hn)
    nlinarith [Real.pi_gt_three]
  rw [mul_pow,inv_pow]
  have hN' : ‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖^2 ≤ 100 := by
    nlinarith [sq_nonneg (‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖)]
  rw [← div_eq_inv_mul,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hlow)]
  nlinarith [Real.pi_gt_three]
end EuclideanFiveColor
end

end OAI
