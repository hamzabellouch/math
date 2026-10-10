import OAI.Analysis.Mahler.TailIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

namespace SymmetricMahler
open Real MeasureTheory

/-- Exponential majorization on the outer interval. -/
theorem radial_power_bound {m r : ℝ} (hm : 2 ≤ m) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r ^ (2*m-3/2 : ℝ) ≤ exp (-m*(1-r)) := by
  by_cases hz : r = 0
  · rw [hz, zero_rpow (show (2*m-3/2 : ℝ) ≠ 0 by linarith)]
    positivity
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    rw [rpow_def_of_pos hrpos]
    apply exp_le_exp.mpr
    have hlog := log_le_sub_one_of_pos hrpos
    have hsign := log_nonpos hr hr1
    have hneg := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ m-3/2 by linarith) hsign
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ m by linarith)
    nlinarith

end SymmetricMahler

namespace SymmetricMahler
open Real

/-- The radial derivative formula on 0<r<1.
Its removable value at r=0 is not asserted by this definition. -/
noncomputable def radialDerivative (r : ℝ) : ℝ :=
  4 / (Real.pi^2*r) * log ((1+r)/(1-r))

lemma log_le_half {x : ℝ} (hx : 0 < x) : log x ≤ x/2 := by
  have h := log_le_sub_one_of_pos (show 0 < x/2 by positivity)
  rw [log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  have h2 := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

lemma radial_log_lower {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r ≤ log ((1+r)/(1-r)) := by
  have hd : 0 < 1-r := by linarith
  have hfrac : 1/(1-r) ≤ (1+r)/(1-r) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hlog := log_le_log (one_div_pos.mpr hd) hfrac
  rw [one_div, log_inv] at hlog
  have hlin := log_le_sub_one_of_pos hd
  linarith

/-- A concrete global positive lower bound for the radial derivative. -/
theorem radial_derivative_lower {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    4/Real.pi^2 ≤ radialDerivative r := by
  have hratio : 1 ≤ log ((1+r)/(1-r))/r :=
    (le_div_iff₀ hr).2 (by simpa using radial_log_lower hr hr1)
  have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4/Real.pi^2 by positivity)
  calc
    4/Real.pi^2 = (4/Real.pi^2)*1 := (mul_one _).symm
    _ ≤ (4/Real.pi^2)*(log ((1+r)/(1-r))/r) := h
    _ = radialDerivative r := by dsimp [radialDerivative]; field_simp

/-- The logarithmic boundary layer starts at 1-log(m)/m. -/
lemma boundary_layer_log_lower {m r : ℝ} (hm : 1 < m)
    (hr : 0 < r) (hr1 : r < 1) (hlayer : 1-log m/m ≤ r) :
    log m/2 ≤ log ((1+r)/(1-r)) := by
  have hmpos : 0 < m := by linarith
  have hlm : 0 < log m := log_pos hm
  have hd : 0 < 1-r := by linarith
  have hgap : (1-r)*m ≤ log m := (le_div_iff₀ hmpos).1 (by linarith : 1-r ≤ log m/m)
  have hfrac : m/log m ≤ 1/(1-r) :=
    (div_le_div_iff₀ hlm hd).2 (by nlinarith)
  have hlog := log_le_log (div_pos hmpos hlm) hfrac
  rw [log_div hmpos.ne' hlm.ne', one_div, log_inv] at hlog
  have hh := log_le_half hlm
  have hfrac2 : 1/(1-r) ≤ (1+r)/(1-r) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hlog2 := log_le_log (one_div_pos.mpr hd) hfrac2
  rw [one_div, log_inv] at hlog2
  linarith

/-- The estimate M'≥c log m holds with c=2/π². -/
theorem boundary_layer_derivative_lower {m r : ℝ} (hm : 1 < m)
    (hr : 0 < r) (hr1 : r < 1) (hlayer : 1-log m/m ≤ r) :
    (2/Real.pi^2)*log m ≤ radialDerivative r := by
  have hlm : 0 < log m := log_pos hm
  have hlog := boundary_layer_log_lower hm hr hr1 hlayer
  have hratio : log m/2 ≤ log ((1+r)/(1-r))/r := by
    apply (le_div_iff₀ hr).2
    nlinarith
  have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4/Real.pi^2 by positivity)
  calc
    (2/Real.pi^2)*log m = (4/Real.pi^2)*(log m/2) := by ring
    _ ≤ (4/Real.pi^2)*(log ((1+r)/(1-r))/r) := h
    _ = radialDerivative r := by dsimp [radialDerivative]; field_simp

end SymmetricMahler

namespace SymmetricMahler
open Real Set

/-- The global M-increment estimate obtained from the actual radial derivative,
with only open-interval derivatives required, including when the left endpoint is 0. -/
theorem radial_increment_lower {M : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    (hcont : ContinuousOn M (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt M (radialDerivative x) x) :
    (4/Real.pi^2)*(b-a) ≤ M b-M a := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    simp
  · obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope M radialDerivative hlt hcont hderiv
    have hlow := radial_derivative_lower (show 0 < x by linarith [hx.1])
      (show x < 1 by linarith [hx.2])
    rw [heq] at hlow
    exact (le_div_iff₀ (sub_pos.mpr hlt)).1 hlow

/-- The strengthened increment estimate inside the logarithmic boundary layer. -/
theorem boundary_layer_increment_lower {M : ℝ → ℝ} {m a b : ℝ}
    (hm : 1 < m) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    (hlayer : 1-log m/m ≤ a)
    (hcont : ContinuousOn M (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt M (radialDerivative x) x) :
    ((2/Real.pi^2)*log m)*(b-a) ≤ M b-M a := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    simp
  · obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope M radialDerivative hlt hcont hderiv
    have hlow := boundary_layer_derivative_lower hm
      (show 0 < x by linarith [hx.1]) (show x < 1 by linarith [hx.2])
      (show 1-log m/m ≤ x by linarith [hx.1])
    rw [heq] at hlow
    exact (le_div_iff₀ (sub_pos.mpr hlt)).1 hlow

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set

/-- The unscaled error integrand. -/
noncomputable def errorIntegrand (M : ℝ → ℝ) (r₀ m r : ℝ) : ℝ :=
  m * r^(2*m-3/2 : ℝ) * sqrt (1-r^2) / sqrt (M r-M r₀)

/-- Pointwise domination by the exactly integrated outer-tail kernel.
Here c is the lower slope for M on the boundary layer. -/
theorem error_integrand_outer_bound {M : ℝ → ℝ} {r₀ m c b r : ℝ}
    (hm : 2 ≤ m) (hc : 0 < c) (hr : 0 ≤ r) (hbr : b < r) (hr1 : r < 1)
    (hincrement : c*(r-b) ≤ M r-M r₀) :
    errorIntegrand M r₀ m r ≤ sqrt (2/c) *
      (m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := by
  have hden : 0 < c*(r-b) := mul_pos hc (sub_pos.mpr hbr)
  have hM : 0 < M r-M r₀ := lt_of_lt_of_le hden hincrement
  have hnum : 0 ≤ 1-r^2 := by nlinarith
  have hratio : (1-r^2)/(M r-M r₀) ≤ (2/c)*((1-r)/(r-b)) := by
    calc
      _ ≤ (1-r^2)/(c*(r-b)) := div_le_div_of_nonneg_left hnum hden hincrement
      _ ≤ (2*(1-r))/(c*(r-b)) :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (1-r)]) hden.le
      _ = (2/c)*((1-r)/(r-b)) := by field_simp
  have hs := sqrt_le_sqrt hratio
  rw [sqrt_div hnum, sqrt_mul (show 0 ≤ 2/c by positivity)] at hs
  have hpow := radial_power_bound hm hr hr1.le
  calc
    errorIntegrand M r₀ m r = m *
        (r^(2*m-3/2 : ℝ) * (sqrt (1-r^2)/sqrt (M r-M r₀))) := by
      dsimp [errorIntegrand]
      ring
    _ ≤ m * (exp (-m*(1-r)) *
        (sqrt (2/c)*sqrt ((1-r)/(r-b)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hpow hs (by positivity) (exp_nonneg _)) (by linarith)
    _ = sqrt (2/c)*(m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := by ring

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set Filter

/-- Integrability of the original outer error follows from the singular majorant;
measurability is explicit so no unproved integrability is hidden in the integral. -/
theorem outer_error_integrable {M : ℝ → ℝ} {r₀ m c b : ℝ}
    (hM : Measurable M) (hm : 2 ≤ m) (hc : 0 < c) (hb : 0 ≤ b) (hb1 : b < 1)
    (hincrement : ∀ r ∈ Ioo b 1, c*(r-b) ≤ M r-M r₀) :
    IntervalIntegrable (errorIntegrand M r₀ m) volume b 1 := by
  have hmpos : 0 < m := by linarith
  have hg := (rescaled_tail_integrable hmpos hb1).const_mul (sqrt (2/c))
  have hmeas : Measurable (errorIntegrand M r₀ m) := by
    change Measurable (fun r : ℝ => m * r^(2*m-3/2 : ℝ) * sqrt (1-r^2) / sqrt (M r-M r₀))
    fun_prop
  apply hg.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  rw [uIoc_of_le hb1.le] at hr
  have hr0 : 0 ≤ r := by linarith [hr.1]
  rcases hr.2.eq_or_lt with heq | hlt
  · subst r
    simp [errorIntegrand]
  · have hn : 0 ≤ errorIntegrand M r₀ m r := by
      dsimp [errorIntegrand]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact error_integrand_outer_bound hm hc hr0 hr.1 hlt (hincrement r ⟨hr.1,hlt⟩)

/-- The outer portion of the error integral, with an explicit constant. -/
theorem outer_error_integral_bound {M : ℝ → ℝ} {r₀ m c b : ℝ}
    (hM : Measurable M) (hm : 2 ≤ m) (hc : 0 < c) (hb : 0 ≤ b) (hb1 : b < 1)
    (hincrement : ∀ r ∈ Ioo b 1, c*(r-b) ≤ M r-M r₀) :
    (∫ r in b..(1 : ℝ), errorIntegrand M r₀ m r) ≤
      sqrt (2/c)*(1+4/exp 1) := by
  have hmpos : 0 < m := by linarith
  have hf := outer_error_integrable hM hm hc hb hb1 hincrement
  have hg := (rescaled_tail_integrable hmpos hb1).const_mul (sqrt (2/c))
  calc
    _ ≤ ∫ r in b..(1 : ℝ), sqrt (2/c)*
        (m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hb1.le hf hg
      intro r hr
      exact error_integrand_outer_bound hm hc (by linarith [hr.1]) hr.1 hr.2
        (hincrement r hr)
    _ = sqrt (2/c)*(∫ r in b..(1 : ℝ),
        m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := intervalIntegral.integral_const_mul _ _
    _ ≤ sqrt (2/c)*(1+4/exp 1) :=
      mul_le_mul_of_nonneg_left (rescaled_tail_bound hmpos hb1) (sqrt_nonneg _)

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set

/-- The inner error is controlled by an integrable square-root singularity. -/
theorem error_integrand_inner_bound {M : ℝ → ℝ} {r₀ m c b r : ℝ}
    (hm : 2 ≤ m) (hc : 0 < c) (hr : 0 ≤ r) (hr₀ : r₀ < r)
    (hrb : r ≤ b) (_hb1 : b ≤ 1)
    (hincrement : c*(r-r₀) ≤ M r-M r₀) :
    errorIntegrand M r₀ m r ≤
      (m*b^(2*m-3/2 : ℝ)/sqrt c)*(1/sqrt (r-r₀)) := by
  have hb : 0 ≤ b := le_trans hr hrb
  have hden : 0 < sqrt (c*(r-r₀)) := sqrt_pos.2 (mul_pos hc (sub_pos.mpr hr₀))
  have hM : sqrt (c*(r-r₀)) ≤ sqrt (M r-M r₀) := sqrt_le_sqrt hincrement
  have hpow : r^(2*m-3/2 : ℝ) ≤ b^(2*m-3/2 : ℝ) :=
    rpow_le_rpow hr hrb (by linarith)
  have hnum : sqrt (1-r^2) ≤ 1 := by
    apply sqrt_le_iff.2
    exact ⟨by norm_num, by nlinarith [sq_nonneg r]⟩
  have hprod : m*r^(2*m-3/2 : ℝ)*sqrt (1-r^2) ≤ m*b^(2*m-3/2 : ℝ) := by
    have h := mul_le_mul hpow hnum (sqrt_nonneg _) (rpow_nonneg hb _)
    nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ m by linarith)]
  calc
    errorIntegrand M r₀ m r ≤ m*b^(2*m-3/2 : ℝ)/sqrt (M r-M r₀) :=
      div_le_div_of_nonneg_right hprod (sqrt_nonneg _)
    _ ≤ m*b^(2*m-3/2 : ℝ)/sqrt (c*(r-r₀)) :=
      div_le_div_of_nonneg_left (by positivity) hden hM
    _ = (m*b^(2*m-3/2 : ℝ)/sqrt c)*(1/sqrt (r-r₀)) := by
      rw [sqrt_mul hc.le]
      field_simp

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set Filter

/-- Integrability of the inner portion follows from the square-root majorant. -/
theorem inner_error_integrable {M : ℝ → ℝ} {r₀ m c b : ℝ}
    (hM : Measurable M) (hm : 2 ≤ m) (hc : 0 < c)
    (hr₀ : 0 ≤ r₀) (hr₀b : r₀ ≤ b) (hb1 : b ≤ 1)
    (hincrement : ∀ r ∈ Ioc r₀ b, c*(r-r₀) ≤ M r-M r₀) :
    IntervalIntegrable (errorIntegrand M r₀ m) volume r₀ b := by
  have hb : 0 ≤ b := le_trans hr₀ hr₀b
  have hg := (right_inverse_sqrt_integrable hr₀b).const_mul
    (m*b^(2*m-3/2 : ℝ)/sqrt c)
  have hmeas : Measurable (errorIntegrand M r₀ m) := by
    change Measurable (fun r : ℝ => m * r^(2*m-3/2 : ℝ) * sqrt (1-r^2) / sqrt (M r-M r₀))
    fun_prop
  apply hg.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  rw [uIoc_of_le hr₀b] at hr
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hn : 0 ≤ errorIntegrand M r₀ m r := by
    dsimp [errorIntegrand]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact error_integrand_inner_bound hm hc hr0 hr.1 hr.2 hb1 (hincrement r hr)

/-- The bound on the inner portion of the error integral, with its constant. -/
theorem inner_error_integral_bound {M : ℝ → ℝ} {r₀ m c b : ℝ}
    (hM : Measurable M) (hm : 2 ≤ m) (hc : 0 < c)
    (hr₀ : 0 ≤ r₀) (hr₀b : r₀ ≤ b) (hb1 : b ≤ 1)
    (hincrement : ∀ r ∈ Ioc r₀ b, c*(r-r₀) ≤ M r-M r₀) :
    (∫ r in r₀..b, errorIntegrand M r₀ m r) ≤ 2*m*b^(2*m-3/2 : ℝ)/sqrt c := by
  have hb : 0 ≤ b := le_trans hr₀ hr₀b
  have hf := inner_error_integrable hM hm hc hr₀ hr₀b hb1 hincrement
  have hg := (right_inverse_sqrt_integrable hr₀b).const_mul
    (m*b^(2*m-3/2 : ℝ)/sqrt c)
  have hcoeff : 0 ≤ m*b^(2*m-3/2 : ℝ)/sqrt c := by positivity
  calc
    _ ≤ ∫ r in r₀..b, (m*b^(2*m-3/2 : ℝ)/sqrt c)*(1/sqrt (r-r₀)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hr₀b hf hg
      intro r hr
      exact error_integrand_inner_bound hm hc (by linarith [hr.1]) hr.1 hr.2.le hb1
        (hincrement r ⟨hr.1,hr.2.le⟩)
    _ = (m*b^(2*m-3/2 : ℝ)/sqrt c)*(2*sqrt (b-r₀)) := by
      rw [intervalIntegral.integral_const_mul, right_inverse_sqrt_integral hr₀b]
    _ ≤ (m*b^(2*m-3/2 : ℝ)/sqrt c)*2 := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      have hs : sqrt (b-r₀) ≤ 1 := sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
      linarith
    _ = 2*m*b^(2*m-3/2 : ℝ)/sqrt c := by ring

end SymmetricMahler

end OAI
