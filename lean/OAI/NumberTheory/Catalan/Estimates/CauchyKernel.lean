import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Analysis.BlaschkeAnalytic
import OAI.NumberTheory.Catalan.Estimates.BlaschkeScalar
import OAI.NumberTheory.Catalan.Estimates.CauchyNumerics

namespace OAI

noncomputable section

namespace InternalCatalan

section

open scoped BigOperators

theorem blaschkeFactor_imaginary_norm_pos (x : ℝ) {u : ℝ} (hu : 0 < u) :
    0 < ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ := by
  have hp : 0 < ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ ^ 2 := by
    rw [blaschkeFactor_imaginary_norm_sq]
    positivity
  nlinarith [norm_nonneg (blaschkeFactor x (Complex.I * (u : ℂ)))]

theorem blaschkeFactor_imaginary_lower {x u : ℝ}
    (hx : x ^ 2 ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1) :
    u ^ blaschkeWeight x ≤ ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ := by
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hu _)
    (blaschkeFactor_imaginary_norm_pos x hu), Real.log_rpow hu]
  have hlog := congrArg Real.log (blaschkeFactor_imaginary_norm_sq u x)
  rw [Real.log_pow, Real.log_div (by positivity) (by positivity)] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have h := blaschke_factor_log_lower hx hu hu1
  linarith

theorem finiteBlaschke_imaginary_lower {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {u : ℝ} (hx : ∀ i ∈ s, x i ^ 2 ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1) :
    u ^ (∑ i ∈ s, blaschkeWeight (x i)) ≤
      ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ := by
  rw [finiteBlaschke_norm, Real.rpow_sum_of_pos hu]
  exact Finset.prod_le_prod₀ (fun _ _ => (Real.rpow_pos_of_pos hu _).le)
    (fun i hi => blaschkeFactor_imaginary_lower (hx i hi) hu hu1)

theorem finiteBlaschke_inner_quotient_le_one {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) {u : ℝ} (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hD : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ)) :
    ‖(Complex.I * (u : ℂ)) ^ D / finiteBlaschke s x (Complex.I * (u : ℂ))‖ ≤ 1 := by
  have hb := finiteBlaschke_imaginary_lower s x hx hu hu1
  have hp := Real.rpow_pos_of_pos hu (∑ i ∈ s, blaschkeWeight (x i))
  have hbp : 0 < ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ := lt_of_lt_of_le hp hb
  rw [norm_div, norm_pow, norm_mul, Complex.norm_I, Complex.norm_of_nonneg hu.le, one_mul]
  apply (div_le_one₀ hbp).mpr
  calc
    u ^ D = u ^ (D : ℝ) := (Real.rpow_natCast u D).symm
    _ ≤ u ^ (∑ i ∈ s, blaschkeWeight (x i)) :=
      Real.rpow_le_rpow_of_exponent_ge hu hu1 hD
    _ ≤ _ := hb

theorem finiteBlaschke_outer_quotient_le_exp_two {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) {u : ℝ} (hDn : D ≤ n)
    (hx : ∀ i ∈ s, x i ^ 2 ≤ 1) (hu : 1 ≤ u) (hun : u ≤ 1 + 2 / (n : ℝ)) :
    ‖(Complex.I * (u : ℂ)) ^ D / finiteBlaschke s x (Complex.I * (u : ℂ))‖ ≤
      Real.exp 2 := by
  have hb := finiteBlaschke_outer_one_le_norm s x hu hx
  have hbp : 0 < ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ := lt_of_lt_of_le zero_lt_one hb
  have hu0 : 0 ≤ u := by linarith
  rw [norm_div, norm_pow, norm_mul, Complex.norm_I, Complex.norm_of_nonneg hu0, one_mul]
  calc
    u ^ D / ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ ≤ u ^ D := by
      apply (div_le_iff₀ hbp).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (pow_nonneg hu0 D)
    _ ≤ Real.exp 2 := outer_diameter_power_le_exp_two hDn hu hun

theorem finiteBlaschke_imaginary_norm_abs {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (u : ℝ) :
    ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ =
      ‖finiteBlaschke s x (Complex.I * ((|u| : ℝ) : ℂ))‖ := by
  rw [finiteBlaschke_norm, finiteBlaschke_norm]
  apply Finset.prod_congr rfl
  intro i _
  have hsq : ‖blaschkeFactor (x i) (Complex.I * (u : ℂ))‖ ^ 2 =
      ‖blaschkeFactor (x i) (Complex.I * ((|u| : ℝ) : ℂ))‖ ^ 2 := by
    rw [blaschkeFactor_imaginary_norm_sq, blaschkeFactor_imaginary_norm_sq, sq_abs]
  nlinarith [norm_nonneg (blaschkeFactor (x i) (Complex.I * (u : ℂ))),
    norm_nonneg (blaschkeFactor (x i) (Complex.I * ((|u| : ℝ) : ℂ)))]

theorem finiteBlaschke_quotient_imaginary_norm_abs {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (u : ℝ) :
    ‖(Complex.I * (u : ℂ)) ^ D / finiteBlaschke s x (Complex.I * (u : ℂ))‖ =
      ‖(Complex.I * ((|u| : ℝ) : ℂ)) ^ D /
        finiteBlaschke s x (Complex.I * ((|u| : ℝ) : ℂ))‖ := by
  simp only [norm_div, norm_pow, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, one_mul, abs_abs]
  rw [finiteBlaschke_imaginary_norm_abs s x u]

theorem finiteBlaschke_diameter_quotient_le_exp_two {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) {u : ℝ} (hDpos : 0 < D) (hDn : D ≤ n)
    (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hD : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    (hu : |u| ≤ 1 + 2 / (n : ℝ)) :
    ‖(Complex.I * (u : ℂ)) ^ D / finiteBlaschke s x (Complex.I * (u : ℂ))‖ ≤
      Real.exp 2 := by
  rw [finiteBlaschke_quotient_imaginary_norm_abs s x D u]
  rcases eq_or_lt_of_le (abs_nonneg u) with hz | hp
  · rw [← hz]
    simpa only [Complex.ofReal_zero, mul_zero, zero_pow hDpos.ne', zero_div, norm_zero] using
      (Real.exp_pos 2).le
  · by_cases hi : |u| ≤ 1
    · exact (finiteBlaschke_inner_quotient_le_one s x D hx hp hi hD).trans
        (by simpa only [Real.exp_zero] using
          (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 by norm_num)))
    · exact finiteBlaschke_outer_quotient_le_exp_two s x D n hDn hx (le_of_not_ge hi) hu

end

section

open MeasureTheory Set
open scoped BigOperators Interval

def blaschkeDensity {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D : ℕ) (z : ℂ) : ℂ :=
  z ^ D / finiteBlaschke s x z

def blaschkeCauchyTransform {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
      (6 * blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) * Complex.I

theorem imaginary_sub_ne_zero_of_re_ne_zero {z : ℂ} (hz : z.re ≠ 0) (t : ℝ) :
    Complex.I * (t : ℂ) - z ≠ 0 := by
  intro h
  have hre : -z.re = 0 := by
    simpa [Complex.mul_re, Complex.mul_im] using congrArg Complex.re h
  exact hz (neg_eq_zero.mp hre)

theorem abs_re_le_norm_imaginary_sub (z : ℂ) (t : ℝ) :
    |z.re| ≤ ‖Complex.I * (t : ℂ) - z‖ := by
  simpa [Complex.mul_re, Complex.mul_im] using
    Complex.abs_re_le_norm (Complex.I * (t : ℂ) - z)

theorem continuous_blaschkeDensity_imaginary {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) :
    Continuous (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ))) := by
  have hpath : Continuous (fun t : ℝ => Complex.I * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  apply continuous_iff_continuousAt.mpr
  intro t
  change ContinuousAt
    (fun t : ℝ => (Complex.I * (t : ℂ)) ^ D /
      finiteBlaschke s x (Complex.I * (t : ℂ))) t
  have houter : ContinuousAt (fun w : ℂ => w ^ D / finiteBlaschke s x w)
      (Complex.I * (t : ℂ)) :=
    (finiteBlaschke_quotient_analyticAt_imaginary s x D hx t).continuousAt
  have hinner : ContinuousAt (fun u : ℝ => Complex.I * (u : ℂ)) t := hpath.continuousAt
  simpa only [Function.comp_def] using
    houter.comp (f := fun u : ℝ => Complex.I * (u : ℂ)) hinner

theorem continuous_blaschkeCauchyKernel {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ} (hz : z.re ≠ 0) :
    Continuous (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)) := by
  exact (continuous_blaschkeDensity_imaginary s x D hx).div
    ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const)
    (imaginary_sub_ne_zero_of_re_ne_zero hz)

theorem intervalIntegrable_blaschkeCauchyIntegrand {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ} (hz : z.re ≠ 0) :
    IntervalIntegrable (fun t : ℝ =>
      (6 * blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) * Complex.I)
      volume (-(1 + 2 / (n : ℝ))) (1 + 2 / (n : ℝ)) := by
  have hc : Continuous (fun t : ℝ =>
      (6 * blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) * Complex.I) := by
    simpa only [mul_div_assoc] using
      ((continuous_blaschkeCauchyKernel s x D hx hz).const_mul (6 : ℂ)).mul_const Complex.I
  exact hc.intervalIntegrable _ _

theorem blaschkeCauchyTransform_normalized {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (z : ℂ) :
    blaschkeCauchyTransform s x D n z = ((3 / Real.pi : ℝ) : ℂ) *
      ∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
        blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z) := by
  have hfun : (fun t : ℝ =>
      (6 * blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) * Complex.I) =
      (fun t : ℝ => (6 * Complex.I) *
        (blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z))) := by
    funext t
    ring
  have hp : (Real.pi : ℂ) ≠ 0 := by
    intro h
    exact Real.pi_pos.ne' (by simpa using congrArg Complex.re h)
  have hcoeff : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (6 * Complex.I) =
      ((3 / Real.pi : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    field_simp [hp, Complex.I_ne_zero]
    ring
  unfold blaschkeCauchyTransform
  rw [hfun, intervalIntegral.integral_const_mul, ← mul_assoc, hcoeff]

theorem blaschkeCauchyTransform_norm_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hDpos : 0 < D) (hDn : D ≤ n)
    (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hD : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : z.re ≠ 0) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) * Real.exp 2 / |z.re| := by
  let T : ℝ := 1 + 2 / (n : ℝ)
  have hT : 0 < T := by dsimp only [T]; positivity
  have hzr : 0 < |z.re| := abs_pos.mpr hz
  have hi : ‖∫ t in -T..T,
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      (Real.exp 2 / |z.re|) * (2 * T) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T) (C := Real.exp 2 / |z.re|)
      (f := fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) (fun t ht => by
          have ht' : t ∈ Ioc (-T) T := by
            simpa only [uIoc_of_le (show -T ≤ T by linarith)] using ht
          have htab : |t| ≤ 1 + 2 / (n : ℝ) := abs_le.mpr ⟨ht'.1.le, ht'.2⟩
          have hf : ‖blaschkeDensity s x D (Complex.I * (t : ℂ))‖ ≤ Real.exp 2 :=
            finiteBlaschke_diameter_quotient_le_exp_two s x D n hDpos hDn hx hD htab
          have hdist := abs_re_le_norm_imaginary_sub z t
          have hdistpos : 0 < ‖Complex.I * (t : ℂ) - z‖ := lt_of_lt_of_le hzr hdist
          rw [norm_div]
          exact (div_le_div_of_nonneg_right hf hdistpos.le).trans
            (div_le_div_of_nonneg_left (Real.exp_pos 2).le hzr hdist))
    have hlen : |T - -T| = 2 * T := by rw [abs_of_pos (by linarith)]; ring
    simpa only [hlen] using hbound
  rw [blaschkeCauchyTransform_normalized, norm_mul,
    Complex.norm_of_nonneg (show 0 ≤ 3 / Real.pi by positivity)]
  calc
    (3 / Real.pi) * ‖∫ t in -(1 + 2 / (n : ℝ))..(1 + 2 / (n : ℝ)),
        blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖
      ≤ (3 / Real.pi) * ((Real.exp 2 / |z.re|) * (2 * T)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (3 / Real.pi) * (2 * (1 + 2 / (n : ℝ))) * Real.exp 2 / |z.re| := by
      dsimp only [T]
      ring

theorem blaschkeCauchyTransform_far_axis_bound {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n) (hDpos : 0 < D) (hDn : D ≤ n)
    (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hD : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : 1 / (10 * (n : ℝ)) ≤ |z.re|) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤ 30 * Real.exp 2 * (n : ℝ) := by
  have hz0 : z.re ≠ 0 := abs_pos.mp (cauchy_radius_pos hn hz)
  exact (blaschkeCauchyTransform_norm_le s x D n hDpos hDn hx hD hz0).trans
    (cauchy_exp_two_bound hn hz)

end

section

open MeasureTheory Set Metric
open scoped Topology Interval

def blaschkeCauchySegment (n : ℕ) : Set ℂ :=
  (fun t : ℝ => Complex.I * (t : ℂ)) ''
    Icc (-(1 + 2 / (n : ℝ))) (1 + 2 / (n : ℝ))

theorem isCompact_blaschkeCauchySegment (n : ℕ) : IsCompact (blaschkeCauchySegment n) := by
  unfold blaschkeCauchySegment
  exact isCompact_Icc.image (continuous_const.mul Complex.continuous_ofReal)

theorem imaginary_sub_ne_zero_of_not_mem_blaschkeCauchySegment {n : ℕ} {z : ℂ}
    (hz : z ∉ blaschkeCauchySegment n) {t : ℝ}
    (ht : t ∈ Icc (-(1 + 2 / (n : ℝ))) (1 + 2 / (n : ℝ))) :
    Complex.I * (t : ℂ) - z ≠ 0 := by
  intro h
  apply hz
  exact ⟨t, ht, sub_eq_zero.mp h⟩

theorem exists_blaschkeCauchySegment_separation {n : ℕ} {z : ℂ}
    (hz : z ∉ blaschkeCauchySegment n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ blaschkeCauchySegment n, δ ≤ ‖w - z‖ := by
  have hopen : IsOpen (blaschkeCauchySegment n)ᶜ :=
    (isCompact_blaschkeCauchySegment n).isClosed.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  by_contra h
  have hd : dist w z < δ := by simpa only [dist_eq_norm] using lt_of_not_ge h
  exact (hball (Metric.mem_ball.mpr hd)) hw

theorem exists_blaschkeCauchySegment_uniform_separation {n : ℕ} {z₀ : ℂ}
    (hz : z₀ ∉ blaschkeCauchySegment n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball z₀ (δ / 2),
      ∀ t ∈ Icc (-(1 + 2 / (n : ℝ))) (1 + 2 / (n : ℝ)),
        δ / 2 ≤ ‖Complex.I * (t : ℂ) - z‖ := by
  obtain ⟨δ, hδ, hsep⟩ := exists_blaschkeCauchySegment_separation hz
  refine ⟨δ, hδ, ?_⟩
  intro z hznear t ht
  have hbase := hsep (Complex.I * (t : ℂ)) ⟨t, ht, rfl⟩
  have hnear : ‖z - z₀‖ < δ / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hznear
  have htri : ‖Complex.I * (t : ℂ) - z₀‖ ≤
      ‖Complex.I * (t : ℂ) - z‖ + ‖z - z₀‖ := by
    simpa only [dist_eq_norm] using dist_triangle (Complex.I * (t : ℂ)) z z₀
  linarith

theorem continuousOn_blaschkeCauchyKernel_off_segment {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : z ∉ blaschkeCauchySegment n) :
    ContinuousOn (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z))
      (Icc (-(1 + 2 / (n : ℝ))) (1 + 2 / (n : ℝ))) := by
  exact (continuous_blaschkeDensity_imaginary s x D hx).continuousOn.div
    ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).continuousOn
    (fun t ht => imaginary_sub_ne_zero_of_not_mem_blaschkeCauchySegment hz ht)

theorem intervalIntegrable_blaschkeCauchyKernel_off_segment {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : z ∉ blaschkeCauchySegment n) :
    IntervalIntegrable (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z))
      volume (-(1 + 2 / (n : ℝ))) (1 + 2 / (n : ℝ)) := by
  have hT : 0 ≤ 1 + 2 / (n : ℝ) := by positivity
  exact ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    (continuousOn_blaschkeCauchyKernel_off_segment s x D n hx hz)

theorem intervalIntegrable_blaschkeCauchyIntegrand_off_segment {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : z ∉ blaschkeCauchySegment n) :
    IntervalIntegrable (fun t : ℝ =>
      (6 * blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) * Complex.I)
      volume (-(1 + 2 / (n : ℝ))) (1 + 2 / (n : ℝ)) := by
  have hT : 0 ≤ 1 + 2 / (n : ℝ) := by positivity
  have hc : ContinuousOn (fun t : ℝ =>
      (6 * blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)) * Complex.I)
      (Icc (-(1 + 2 / (n : ℝ))) (1 + 2 / (n : ℝ))) := by
    simpa only [mul_div_assoc] using
      ((continuousOn_blaschkeCauchyKernel_off_segment s x D n hx hz).const_mul (6 : ℂ)).mul_const
        Complex.I
  exact ContinuousOn.intervalIntegrable_of_Icc (by linarith) hc

end

open scoped BigOperators

theorem blaschkeCauchyKernel_hasDerivAt {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (t : ℝ) (z : ℂ) (hden : Complex.I * (t : ℂ) - z ≠ 0) :
    HasDerivAt
      (fun w : ℂ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - w))
      (blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z) ^ 2) z := by
  have hd := HasDerivAt.const_sub (Complex.I * (t : ℂ)) (hasDerivAt_id z)
  have h := (hasDerivAt_const z (blaschkeDensity s x D (Complex.I * (t : ℂ)))).fun_div
    hd hden
  convert! h using 1
  simp only [id_eq, zero_mul, mul_neg_one, zero_sub, neg_neg]

theorem blaschkeCauchyKernel_derivative_norm_le {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) (t : ℝ) (z : ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hsep : δ / 2 ≤ ‖Complex.I * (t : ℂ) - z‖) :
    ‖blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z) ^ 2‖ ≤
      ‖blaschkeDensity s x D (Complex.I * (t : ℂ))‖ * (4 / δ ^ 2) := by
  rw [norm_div, norm_pow]
  have hsq : (δ / 2) ^ 2 ≤ ‖Complex.I * (t : ℂ) - z‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hsep
  calc
    _ ≤ ‖blaschkeDensity s x D (Complex.I * (t : ℂ))‖ / (δ / 2) ^ 2 :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hsq
    _ = ‖blaschkeDensity s x D (Complex.I * (t : ℂ))‖ * (4 / δ ^ 2) := by
      field_simp [hδ.ne']
      ring

end InternalCatalan

end

end OAI
