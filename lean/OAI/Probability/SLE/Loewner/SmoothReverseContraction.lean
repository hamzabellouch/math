import OAI.Probability.SLE.Loewner.SmoothReverseLoewner

namespace OAI

/-! Short reverse trajectories from the vertical line over a smooth
driver contract. This gives a uniform Cauchy estimate at zero starting
height without assuming that a trace already exists. -/
noncomputable section
open Set Filter Complex MeasureTheory
open scoped Topology

namespace SLEExactGauge

theorem smooth_reverse_trajectories_contract {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (q r : ℝ → ℂ) (u u' : ℝ → ℝ)
    (hq : ∀ t ∈ Icc 0 T, HasDerivWithinAt q (-2/(q t-(u t : ℂ))) (Icc 0 T) t)
    (hr : ∀ t ∈ Icc 0 T, HasDerivWithinAt r (-2/(r t-(u t : ℂ))) (Icc 0 T) t)
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (u' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, |u' t| ≤ L)
    (hqp : ∀ t ∈ Icc 0 T, 0 < (q t).im)
    (hrp : ∀ t ∈ Icc 0 T, 0 < (r t).im)
    (hq0 : (q 0).re=u 0) (hr0 : (r 0).re=u 0)
    (hsmall : L^2*T ≤ 1) : dist (q T) (r T) ≤ dist (q 0) (r 0) := by
  have hqc : ContinuousOn q (Icc 0 T) := fun t ht => (hq t ht).continuousWithinAt
  have hrc : ContinuousOn r (Icc 0 T) := fun t ht => (hr t ht).continuousWithinAt
  have huc : ContinuousOn u (Icc 0 T) := fun t ht => (hu t ht).continuousWithinAt
  have hqx := (reverse_centered_coordinates hL q u u' hq hu hb hqp hq0).1
  have hrx := (reverse_centered_coordinates hL r u u' hr hu hb hrp hr0).1
  have hqy := reverse_loewner_height_lower hL q u u' hq hu hb hqp hq0 hsmall
  have hry := reverse_loewner_height_lower hL r u u' hr hu hb hrp hr0 hsmall
  let c (t : ℝ) : ℂ := 2/((q t-(u t : ℂ))*(r t-(u t : ℂ)))
  have hqn (t : ℝ) (ht : t ∈ Icc 0 T) : q t-(u t : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hh
    exact (hqp t ht).ne' hh
  have hrn (t : ℝ) (ht : t ∈ Icc 0 T) : r t-(u t : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hh
    exact (hrp t ht).ne' hh
  have hc : ContinuousOn c (Icc 0 T) := continuousOn_const.div
    ((hqc.sub (Complex.continuous_ofReal.comp_continuousOn huc)).mul
      (hrc.sub (Complex.continuous_ofReal.comp_continuousOn huc)))
    (fun t ht => mul_ne_zero (hqn t ht) (hrn t ht))
  have hcn (t : ℝ) (ht : t ∈ Icc 0 T) : (c t).re ≤ 0 := by
    have hprod : ((q t).re-u t)*((r t).re-u t) ≤ (L*t)^2 := by
      calc
        _ ≤ |((q t).re-u t)*((r t).re-u t)| := le_abs_self _
        _ = |(q t).re-u t| * |(r t).re-u t| := abs_mul _ _
        _ ≤ (L*t)*(L*t) := mul_le_mul (hqx t ht) (hrx t ht)
          (abs_nonneg _) (mul_nonneg hL ht.1)
        _ = _ := (pow_two _).symm
    have hroot : (Real.sqrt (2*t))^2=2*t := Real.sq_sqrt (mul_nonneg (by norm_num) ht.1)
    have hqroot : Real.sqrt (2*t) ≤ (q t).im := by
      nlinarith [Real.sqrt_nonneg (2*t),hqp t ht,hqy t ht]
    have hrroot : Real.sqrt (2*t) ≤ (r t).im := by
      nlinarith [Real.sqrt_nonneg (2*t),hrp t ht,hry t ht]
    have hyy : 2*t ≤ (q t).im*(r t).im := by
      nlinarith [mul_le_mul hqroot hrroot (Real.sqrt_nonneg (2*t)) (hqp t ht).le]
    have hsmallt := (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg L)).trans hsmall
    have hxx : ((q t).re-u t)*((r t).re-u t) ≤ t := by
      nlinarith [mul_le_mul_of_nonneg_right hsmallt ht.1]
    have hreal : ((q t-(u t : ℂ))*(r t-(u t : ℂ))).re ≤ 0 := by
      simp only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,
        Complex.sub_im,Complex.ofReal_im,sub_zero]
      linarith [ht.1]
    dsimp [c]
    simp only [Complex.div_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,zero_div,add_zero]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith
    · exact Complex.normSq_nonneg _
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt (fun s => q s-r s)
      (c t*(q t-r t)) (Icc 0 T) t := by
    convert (hq t ht).sub (hr t ht) using 1
    dsimp [c]
    field_simp [hqn t ht,hrn t ht]
    ring
  have he := complex_linear_ode_exp T hT (fun t => q t-r t) c hc hd
  have hi : (∫ t in (0 : ℝ)..T, (c t).re) ≤ 0 := by
    have hh := intervalIntegral.integral_mono_on hT
      ((Complex.continuous_re.comp_continuousOn hc).intervalIntegrable_of_Icc hT)
      (intervalIntegrable_const (μ := volume) (c := (0 : ℝ))) hcn
    simpa only [intervalIntegral.integral_zero,Function.comp_def] using hh
  have hir : (∫ t in (0 : ℝ)..T, (c t).re) = (∫ t in (0 : ℝ)..T, c t).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable_of_Icc hT)
  rw [dist_eq_norm,dist_eq_norm,he,norm_mul,Complex.norm_exp,← hir]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr hi)

end SLEExactGauge

end

end OAI
