import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import OAI.NumberTheory.Catalan.Analysis.BlaschkeCauchyAnalytic
import OAI.NumberTheory.Catalan.Analysis.BlaschkeDensityLogDerivative
import OAI.NumberTheory.Catalan.Analysis.CauchyLocalLogBound

namespace OAI


noncomputable section
namespace InternalCatalan

theorem imaginary_path_dist (t u : ℝ) :
    ‖Complex.I * (t : ℂ) - Complex.I * (u : ℂ)‖ = |t - u| := by
  rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

theorem upper_circle_crossing_location {r : ℝ} {z : ℂ}
    (hz : ‖z‖ = 1) (him : 0 ≤ z.im) (hre : |z.re| ≤ r / 10) :
    1 - r / 10 ≤ z.im ∧ z.im ≤ 1 ∧ ‖z - Complex.I‖ ≤ r / 5 := by
  have himhi : z.im ≤ 1 := by
    calc
      z.im ≤ |z.im| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
      _ = 1 := hz
  have hl := Complex.norm_le_abs_re_add_abs_im z
  rw [hz, abs_of_nonneg him] at hl
  refine ⟨by linarith, himhi, ?_⟩
  have hn := Complex.norm_le_abs_re_add_abs_im (z - Complex.I)
  simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im] at hn
  rw [abs_of_nonpos (sub_nonpos.mpr himhi)] at hn
  linarith

theorem upper_crossing_far_separation {r t : ℝ} {z : ℂ} (hr : 0 ≤ r)
    (hz : 1 - r / 10 ≤ z.im) (ht : t ≤ 1 - r) :
    r / 2 ≤ ‖Complex.I * (t : ℂ) - z‖ := by
  have hv := Complex.abs_im_le_norm (Complex.I * (t : ℂ) - z)
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at hv
  have ha := neg_le_abs (t - z.im)
  linarith

theorem upper_crossing_local_path {r t : ℝ} (hr : 0 ≤ r)
    (htl : 1 - r ≤ t) (htu : t ≤ 1 + 2 * r) :
    ‖Complex.I * (t : ℂ) - Complex.I‖ ≤ 2 * r := by
  have hnorm : ‖Complex.I * (t : ℂ) - Complex.I‖ = |t - 1| := by
    simpa only [Complex.ofReal_one, mul_one] using imaginary_path_dist t 1
  rw [hnorm]
  apply abs_le.mpr
  constructor <;> linarith

theorem upper_crossing_endpoint_distances {r : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hrsmall : r ≤ (1 / 48 : ℝ))
    (hz : ‖z‖ = 1) (him : 0 ≤ z.im) (hre : |z.re| ≤ r / 10) :
    (r / 2 ≤ ‖Complex.I * ((1 - r : ℝ) : ℂ) - z‖ ∧
      ‖Complex.I * ((1 - r : ℝ) : ℂ) - z‖ ≤ 1) ∧
    (r / 2 ≤ ‖Complex.I * ((1 + 2 * r : ℝ) : ℂ) - z‖ ∧
      ‖Complex.I * ((1 + 2 * r : ℝ) : ℂ) - z‖ ≤ 1) := by
  have hloc := upper_circle_crossing_location hz him hre
  have hu (t : ℝ) (htl : 1 - r ≤ t) (htu : t ≤ 1 + 2 * r) :
      ‖Complex.I * (t : ℂ) - z‖ ≤ 1 := by
    have htri := norm_add_le (Complex.I * (t : ℂ) - Complex.I) (Complex.I - z)
    have heq : (Complex.I * (t : ℂ) - Complex.I) + (Complex.I - z) =
        Complex.I * (t : ℂ) - z := by ring
    rw [heq, norm_sub_rev Complex.I z] at htri
    have hp := upper_crossing_local_path hr htl htu
    linarith [hloc.2.2]
  refine ⟨⟨upper_crossing_far_separation hr hloc.1 le_rfl, hu _ le_rfl (by linarith)⟩,
    ⟨?_, hu _ (by linarith) le_rfl⟩⟩
  have hv := Complex.abs_im_le_norm (Complex.I * ((1 + 2 * r : ℝ) : ℂ) - z)
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at hv
  have ha := le_abs_self (1 + 2 * r - z.im)
  linarith [hloc.2.1]

theorem imaginary_path_neg_distance (t : ℝ) (z : ℂ) :
    ‖Complex.I * ((-t : ℝ) : ℂ) - (-z)‖ = ‖Complex.I * (t : ℂ) - z‖ := by
  have heq : Complex.I * ((-t : ℝ) : ℂ) - (-z) = -(Complex.I * (t : ℂ) - z) := by
    simp only [Complex.ofReal_neg]
    ring
  rw [heq, norm_neg]

theorem lower_circle_crossing_location {r : ℝ} {z : ℂ}
    (hz : ‖z‖ = 1) (him : z.im ≤ 0) (hre : |z.re| ≤ r / 10) :
    -1 ≤ z.im ∧ z.im ≤ -1 + r / 10 ∧ ‖z + Complex.I‖ ≤ r / 5 := by
  have hh := upper_circle_crossing_location (z := -z)
    (by simpa only [norm_neg] using hz)
    (by simpa only [Complex.neg_im] using neg_nonneg.mpr him)
    (by simpa only [Complex.neg_re, abs_neg] using hre)
  have heq : -z - Complex.I = -(z + Complex.I) := by ring
  rw [heq, norm_neg] at hh
  simp only [Complex.neg_im] at hh
  exact ⟨by linarith [hh.2.1], by linarith [hh.1], hh.2.2⟩

theorem lower_crossing_far_separation {r t : ℝ} {z : ℂ} (hr : 0 ≤ r)
    (hz : z.im ≤ -1 + r / 10) (ht : -1 + r ≤ t) :
    r / 2 ≤ ‖Complex.I * (t : ℂ) - z‖ := by
  have hh := upper_crossing_far_separation (z := -z) (t := -t) hr
    (by simp only [Complex.neg_im]; linarith) (by linarith)
  rwa [imaginary_path_neg_distance] at hh

theorem lower_crossing_local_path {r t : ℝ} (hr : 0 ≤ r)
    (htl : -1 - 2 * r ≤ t) (htu : t ≤ -1 + r) :
    ‖Complex.I * (t : ℂ) + Complex.I‖ ≤ 2 * r := by
  have hh := upper_crossing_local_path (t := -t) hr (by linarith) (by linarith)
  have heq : Complex.I * ((-t : ℝ) : ℂ) - Complex.I =
      -(Complex.I * (t : ℂ) + Complex.I) := by simp only [Complex.ofReal_neg]; ring
  rwa [heq, norm_neg] at hh

theorem lower_crossing_endpoint_distances {r : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hrsmall : r ≤ (1 / 48 : ℝ))
    (hz : ‖z‖ = 1) (him : z.im ≤ 0) (hre : |z.re| ≤ r / 10) :
    (r / 2 ≤ ‖Complex.I * ((-1 - 2 * r : ℝ) : ℂ) - z‖ ∧
      ‖Complex.I * ((-1 - 2 * r : ℝ) : ℂ) - z‖ ≤ 1) ∧
    (r / 2 ≤ ‖Complex.I * ((-1 + r : ℝ) : ℂ) - z‖ ∧
      ‖Complex.I * ((-1 + r : ℝ) : ℂ) - z‖ ≤ 1) := by
  have hh := upper_crossing_endpoint_distances hr hrsmall (z := -z)
    (by simpa only [norm_neg] using hz)
    (by simpa only [Complex.neg_im] using neg_nonneg.mpr him)
    (by simpa only [Complex.neg_re, abs_neg] using hre)
  have heq1 : (1 - r : ℝ) = -(-1 + r) := by ring
  have heq2 : (1 + 2 * r : ℝ) = -(-1 - 2 * r) := by ring
  rw [heq1, heq2, imaginary_path_neg_distance, imaginary_path_neg_distance] at hh
  exact ⟨hh.2, hh.1⟩






def circleRightPerturb (z : ℂ) (t : ℝ) : ℂ :=
  (z + (t : ℂ)) / (‖z + (t : ℂ)‖ : ℂ)

theorem circleRightPerturb_zero {z : ℂ} (hz : ‖z‖ = 1) : circleRightPerturb z 0 = z := by
  simp [circleRightPerturb, hz]

theorem circleRightPerturb_continuousAt_zero {z : ℂ} (hz : ‖z‖ = 1) :
    ContinuousAt (circleRightPerturb z) 0 := by
  have hn : Continuous (fun t : ℝ => z + (t : ℂ)) := continuous_const.add Complex.continuous_ofReal
  have hd : Continuous (fun t : ℝ => (‖z + (t : ℂ)‖ : ℂ)) :=
    Complex.continuous_ofReal.comp hn.norm
  have hd0 : (‖z + ((0 : ℝ) : ℂ)‖ : ℂ) ≠ 0 := by simp [hz]
  exact hn.continuousAt.div hd.continuousAt hd0

theorem circleRightPerturb_norm_and_re {z : ℂ} (hz : z.re = 0) {t : ℝ} (ht : 0 < t) :
    ‖circleRightPerturb z t‖ = 1 ∧ (circleRightPerturb z t).re ≠ 0 := by
  have hv : z + (t : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re, hz, zero_add] at hr
    exact ht.ne' hr
  have hn : ‖z + (t : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnc : (‖z + (t : ℂ)‖ : ℂ) ≠ 0 := by
    intro h
    exact hn (by simpa only [Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re h)
  constructor
  · unfold circleRightPerturb
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hn]
  · intro hzero
    have hm : circleRightPerturb z t * (‖z + (t : ℂ)‖ : ℂ) = z + (t : ℂ) :=
      div_mul_cancel₀ _ hnc
    have hr := congrArg Complex.re hm
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, Complex.add_re, hz, hzero, zero_mul, zero_add] at hr
    exact ht.ne' hr.symm

end InternalCatalan




open Polynomial
open scoped BigOperators
namespace InternalCatalan

def polynomialDividedDifference (p : ℂ[X]) (z w : ℂ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * ∑ j ∈ Finset.range k, z ^ j * w ^ (k - 1 - j)

theorem sub_mul_polynomialDividedDifference (p : ℂ[X]) (z w : ℂ) :
    (w - z) * polynomialDividedDifference p z w = p.eval w - p.eval z := by
  unfold polynomialDividedDifference
  rw [Finset.mul_sum, eval_eq_sum, eval_eq_sum, sum_def, sum_def,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (w - z) * (p.coeff k * ∑ j ∈ Finset.range k, z ^ j * w ^ (k - 1 - j)) =
        p.coeff k * ((w - z) * ∑ j ∈ Finset.range k, z ^ j * w ^ (k - 1 - j)) := by ring
    _ = p.coeff k * (w ^ k - z ^ k) := by rw [(Commute.all z w).mul_neg_geom_sum₂ k]
    _ = p.coeff k * w ^ k - p.coeff k * z ^ k := by ring

theorem polynomialDividedDifference_analyticAt_left (p : ℂ[X]) (w z : ℂ) :
    AnalyticAt ℂ (fun v => polynomialDividedDifference p v w) z := by
  unfold polynomialDividedDifference
  apply Finset.analyticAt_fun_sum
  intro k _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (analyticAt_id.pow j).mul analyticAt_const

theorem polynomialDividedDifference_analyticAt_right (p : ℂ[X]) (z w : ℂ) :
    AnalyticAt ℂ (fun v => polynomialDividedDifference p z v) w := by
  unfold polynomialDividedDifference
  apply Finset.analyticAt_fun_sum
  intro k _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro j _
  exact analyticAt_const.mul (analyticAt_id.pow (k - 1 - j))

theorem polynomialEval_analyticAt (p : ℂ[X]) (z : ℂ) :
    AnalyticAt ℂ (fun v => p.eval v) z := by
  simp only [eval_eq_sum, sum_def]
  apply Finset.analyticAt_fun_sum
  intro k _
  exact analyticAt_const.mul (analyticAt_id.pow k)

def blaschkeDensityRemainder {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (z w : ℂ) : ℂ :=
  (polynomialDividedDifference (blaschkeDensityNumerator s x D) z w *
      (blaschkeNodePolynomial s x).eval z -
    (blaschkeDensityNumerator s x D).eval z *
      polynomialDividedDifference (blaschkeNodePolynomial s x) z w) /
    ((blaschkeNodePolynomial s x).eval w * (blaschkeNodePolynomial s x).eval z)

theorem blaschkeDensity_eq_add_remainder {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) {z w : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0)
    (hw : (blaschkeNodePolynomial s x).eval w ≠ 0) :
    blaschkeDensity s x D w = blaschkeDensity s x D z +
      (w - z) * blaschkeDensityRemainder s x D z w := by
  let A := blaschkeDensityNumerator s x D
  let P := blaschkeNodePolynomial s x
  have hnum : (w - z) *
      (polynomialDividedDifference A z w * P.eval z -
        A.eval z * polynomialDividedDifference P z w) =
      A.eval w * P.eval z - A.eval z * P.eval w := by
    calc
      _ = ((w - z) * polynomialDividedDifference A z w) * P.eval z -
          A.eval z * ((w - z) * polynomialDividedDifference P z w) := by ring
      _ = _ := by rw [sub_mul_polynomialDividedDifference,
                       sub_mul_polynomialDividedDifference]; ring
  rw [blaschkeDensity_eq_eval_div, blaschkeDensity_eq_eval_div]
  change A.eval w / P.eval w = A.eval z / P.eval z + (w - z) *
    ((polynomialDividedDifference A z w * P.eval z -
      A.eval z * polynomialDividedDifference P z w) / (P.eval w * P.eval z))
  rw [← mul_div_assoc, hnum]
  field_simp [show P.eval z ≠ 0 from hz, show P.eval w ≠ 0 from hw]
  ring

theorem blaschkeDensityRemainder_analyticAt_left {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) {z w : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0)
    (hw : (blaschkeNodePolynomial s x).eval w ≠ 0) :
    AnalyticAt ℂ (fun v => blaschkeDensityRemainder s x D v w) z := by
  unfold blaschkeDensityRemainder
  exact (((polynomialDividedDifference_analyticAt_left _ _ _).mul
      (polynomialEval_analyticAt _ _)).sub
    ((polynomialEval_analyticAt _ _).mul
      (polynomialDividedDifference_analyticAt_left _ _ _))).div
    (analyticAt_const.mul (polynomialEval_analyticAt _ _)) (mul_ne_zero hw hz)

theorem blaschkeDensityRemainder_analyticAt_right {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D : ℕ) {z w : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0)
    (hw : (blaschkeNodePolynomial s x).eval w ≠ 0) :
    AnalyticAt ℂ (fun v => blaschkeDensityRemainder s x D z v) w := by
  unfold blaschkeDensityRemainder
  exact (((polynomialDividedDifference_analyticAt_right _ _ _).mul analyticAt_const).sub
    (analyticAt_const.mul (polynomialDividedDifference_analyticAt_right _ _ _))).div
    ((polynomialEval_analyticAt _ _).mul analyticAt_const) (mul_ne_zero hw hz)

end InternalCatalan

end



noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators Interval
namespace InternalCatalan

def blaschkeCauchyMoment {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T : ℝ) (k : ℕ) : ℂ :=
  ∫ t in -T..T, (Complex.I * (t : ℂ)) ^ k /
    (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))

def blaschkeIntegratedDividedDifference {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T : ℝ) (p : ℂ[X]) (z : ℂ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * ∑ j ∈ Finset.range k,
    z ^ j * blaschkeCauchyMoment s x T (k - 1 - j)

private theorem continuous_nodePolynomial_imaginary {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) :
    Continuous (fun t : ℝ => (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) := by
  have hp : Continuous (fun z : ℂ => (blaschkeNodePolynomial s x).eval z) :=
    continuous_iff_continuousAt.mpr (fun z => (polynomialEval_analyticAt _ z).continuousAt)
  exact hp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem continuous_blaschkeCauchyMoment_integrand {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0) (k : ℕ) :
    Continuous (fun t : ℝ => (Complex.I * (t : ℂ)) ^ k /
      (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) := by
  exact ((continuous_const.mul Complex.continuous_ofReal).pow k).div
    (continuous_nodePolynomial_imaginary s x)
    (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx)

theorem intervalIntegrable_blaschkeCauchyMoment_integrand {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0) (T : ℝ) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => (Complex.I * (t : ℂ)) ^ k /
      (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) volume (-T) T :=
  (continuous_blaschkeCauchyMoment_integrand s x hx k).intervalIntegrable _ _

theorem intervalIntegrable_blaschkeDividedDifference_quotient {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0)
    (T : ℝ) (p : ℂ[X]) (z : ℂ) :
    IntervalIntegrable (fun t : ℝ =>
      polynomialDividedDifference p z (Complex.I * (t : ℂ)) /
        (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) volume (-T) T := by
  have hdd : Continuous (fun w : ℂ => polynomialDividedDifference p z w) :=
    continuous_iff_continuousAt.mpr
      (fun w => (polynomialDividedDifference_analyticAt_right p z w).continuousAt)
  have hpath : Continuous (fun t : ℝ => Complex.I * (t : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have hc : Continuous (fun t : ℝ =>
      polynomialDividedDifference p z (Complex.I * (t : ℂ)) /
        (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) :=
    (hdd.comp hpath).div
    (continuous_nodePolynomial_imaginary s x)
    (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx)
  exact hc.intervalIntegrable _ _

theorem integral_blaschkeDividedDifference_quotient {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0)
    (T : ℝ) (p : ℂ[X]) (z : ℂ) :
    (∫ t in -T..T, polynomialDividedDifference p z (Complex.I * (t : ℂ)) /
      (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ))) =
      blaschkeIntegratedDividedDifference s x T p z := by
  have hterm (k j : ℕ) : IntervalIntegrable (fun t : ℝ => z ^ j *
      ((Complex.I * (t : ℂ)) ^ (k - 1 - j) /
        (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ)))) volume (-T) T :=
    (intervalIntegrable_blaschkeCauchyMoment_integrand s x hx T (k - 1 - j)).const_mul _
  have hsum (k : ℕ) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ Finset.range k,
      z ^ j * ((Complex.I * (t : ℂ)) ^ (k - 1 - j) /
        (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ)))) volume (-T) T := by
    convert! IntervalIntegrable.sum (Finset.range k) (fun j _ => hterm k j) using 1
    funext t
    simp only [Finset.sum_apply]
  simp only [polynomialDividedDifference, blaschkeIntegratedDividedDifference,
    Finset.sum_div, mul_div_assoc]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (hsum k).const_mul (p.coeff k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun j _ => hterm k j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem blaschkeIntegratedDividedDifference_analyticAt {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (T : ℝ) (p : ℂ[X]) (z : ℂ) :
    AnalyticAt ℂ (blaschkeIntegratedDividedDifference s x T p) z := by
  unfold blaschkeIntegratedDividedDifference
  apply Finset.analyticAt_fun_sum
  intro k _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (analyticAt_id.pow j).mul analyticAt_const

end InternalCatalan

end



noncomputable section
open MeasureTheory Polynomial
open scoped Interval
namespace InternalCatalan

def blaschkeCauchyRemainder {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  blaschkeIntegratedDividedDifference s x T (blaschkeDensityNumerator s x D) z -
    ((blaschkeDensityNumerator s x D).eval z / (blaschkeNodePolynomial s x).eval z) *
      blaschkeIntegratedDividedDifference s x T (blaschkeNodePolynomial s x) z

theorem blaschkeDensityRemainder_eq_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) {z w : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0)
    (hw : (blaschkeNodePolynomial s x).eval w ≠ 0) :
    blaschkeDensityRemainder s x D z w =
      polynomialDividedDifference (blaschkeDensityNumerator s x D) z w /
        (blaschkeNodePolynomial s x).eval w -
      ((blaschkeDensityNumerator s x D).eval z / (blaschkeNodePolynomial s x).eval z) *
        (polynomialDividedDifference (blaschkeNodePolynomial s x) z w /
          (blaschkeNodePolynomial s x).eval w) := by
  unfold blaschkeDensityRemainder
  field_simp [hz, hw]

private theorem remainder_path_eq {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) :
    (fun t : ℝ => blaschkeDensityRemainder s x D z (Complex.I * (t : ℂ))) =
      (fun t : ℝ =>
        polynomialDividedDifference (blaschkeDensityNumerator s x D) z (Complex.I * (t : ℂ)) /
          (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ)) -
        ((blaschkeDensityNumerator s x D).eval z / (blaschkeNodePolynomial s x).eval z) *
          (polynomialDividedDifference (blaschkeNodePolynomial s x) z (Complex.I * (t : ℂ)) /
            (blaschkeNodePolynomial s x).eval (Complex.I * (t : ℂ)))) := by
  funext t
  exact blaschkeDensityRemainder_eq_sub s x D hz
    (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx t)

theorem intervalIntegrable_blaschkeDensityRemainder {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D : ℕ) (T : ℝ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) :
    IntervalIntegrable (fun t : ℝ => blaschkeDensityRemainder s x D z (Complex.I * (t : ℂ)))
      volume (-T) T := by
  rw [remainder_path_eq s x D hx hz]
  exact (intervalIntegrable_blaschkeDividedDifference_quotient s x hx T _ z).sub
    ((intervalIntegrable_blaschkeDividedDifference_quotient s x hx T _ z).const_mul _)

theorem integral_blaschkeDensityRemainder {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D : ℕ) (T : ℝ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) :
    (∫ t in -T..T, blaschkeDensityRemainder s x D z (Complex.I * (t : ℂ))) =
      blaschkeCauchyRemainder s x D T z := by
  rw [remainder_path_eq s x D hx hz]
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_blaschkeDividedDifference_quotient s x hx T _ z)
    ((intervalIntegrable_blaschkeDividedDifference_quotient s x hx T _ z).const_mul _),
    intervalIntegral.integral_const_mul,
    integral_blaschkeDividedDifference_quotient s x hx,
    integral_blaschkeDividedDifference_quotient s x hx]
  rfl

theorem blaschkeCauchyRemainder_analyticAt {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D : ℕ) (T : ℝ) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) :
    AnalyticAt ℂ (blaschkeCauchyRemainder s x D T) z := by
  unfold blaschkeCauchyRemainder
  exact (blaschkeIntegratedDividedDifference_analyticAt _ _ _ _ _).sub
    (((polynomialEval_analyticAt _ _).div (polynomialEval_analyticAt _ _) hz).mul
      (blaschkeIntegratedDividedDifference_analyticAt _ _ _ _ _))

theorem integral_blaschkeCauchyKernel_eq_scalar_add_remainder {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D : ℕ) (T : ℝ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) (hre : z.re ≠ 0) :
    (∫ t in -T..T, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)) =
      blaschkeDensity s x D z *
        (∫ t in -T..T, (1 : ℂ) / (Complex.I * (t : ℂ) - z)) +
      blaschkeCauchyRemainder s x D T z := by
  have hfun : (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)) =
      (fun t : ℝ => blaschkeDensity s x D z * (1 / (Complex.I * (t : ℂ) - z)) +
        blaschkeDensityRemainder s x D z (Complex.I * (t : ℂ))) := by
    funext t
    rw [blaschkeDensity_eq_add_remainder s x D hz
      (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx t)]
    field_simp [imaginary_sub_ne_zero_of_re_ne_zero hre t]
  rw [hfun, intervalIntegral.integral_add
    ((intervalIntegrable_cauchyConstantKernel T hre).const_mul _)
    (intervalIntegrable_blaschkeDensityRemainder s x D T hx hz),
    intervalIntegral.integral_const_mul, integral_blaschkeDensityRemainder s x D T hx hz]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

private theorem complexLog_analyticAt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    AnalyticAt ℂ Complex.log w := by
  have hd : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
    fun z hz => (Complex.differentiableAt_log hz).differentiableWithinAt
  exact hd.analyticOnNhd Complex.isOpen_slitPlane w hw

theorem cauchyLogLeft_analyticAt {T : ℝ} {z : ℂ} (hlo : -T < z.im) (hhi : z.im < T) :
    AnalyticAt ℂ (cauchyLogLeft T) z := by
  have ha : Complex.I * (T : ℂ) - z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa [Complex.mul_im] using (sub_pos.mpr hhi).ne'
  have hb : -Complex.I * (T : ℂ) - z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    have hn : -T - z.im < 0 := by linarith
    simpa [Complex.mul_im] using hn.ne
  have hfa : AnalyticAt ℂ (fun v : ℂ => Complex.I * (T : ℂ) - v) z :=
    analyticAt_const.sub analyticAt_id
  have hfb : AnalyticAt ℂ (fun v : ℂ => -Complex.I * (T : ℂ) - v) z :=
    analyticAt_const.sub analyticAt_id
  unfold cauchyLogLeft
  exact analyticAt_const.mul
    (((complexLog_analyticAt ha).comp hfa).sub ((complexLog_analyticAt hb).comp hfb))

theorem cauchyLogRight_analyticAt {T : ℝ} {z : ℂ} (hlo : -T < z.im) (hhi : z.im < T) :
    AnalyticAt ℂ (cauchyLogRight T) z := by
  have ha : z - Complex.I * (T : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa [Complex.mul_im] using (sub_neg.mpr hhi).ne
  have hb : z + Complex.I * (T : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    have hp : 0 < z.im + T := by linarith
    simpa [Complex.mul_im] using hp.ne'
  have hfa : AnalyticAt ℂ (fun v : ℂ => v - Complex.I * (T : ℂ)) z :=
    analyticAt_id.sub analyticAt_const
  have hfb : AnalyticAt ℂ (fun v : ℂ => v + Complex.I * (T : ℂ)) z :=
    analyticAt_id.add analyticAt_const
  unfold cauchyLogRight
  exact analyticAt_const.mul
    (((complexLog_analyticAt ha).comp (f := fun v : ℂ => v - Complex.I * (T : ℂ)) hfa).sub
      ((complexLog_analyticAt hb).comp (f := fun v : ℂ => v + Complex.I * (T : ℂ)) hfb))

theorem blaschkeDensity_analyticAt_of_nodePolynomial_ne_zero {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D : ℕ) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) :
    AnalyticAt ℂ (blaschkeDensity s x D) z := by
  have hfun : blaschkeDensity s x D = fun v =>
      (blaschkeDensityNumerator s x D).eval v / (blaschkeNodePolynomial s x).eval v :=
    funext (blaschkeDensity_eq_eval_div s x D)
  rw [hfun]
  exact (polynomialEval_analyticAt _ _).div (polynomialEval_analyticAt _ _) hz

def blaschkeCauchyLeft {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (z : ℂ) : ℂ :=
  ((3 / Real.pi : ℝ) : ℂ) *
    (blaschkeDensity s x D z * cauchyLogLeft (1 + 2 / (n : ℝ)) z +
      blaschkeCauchyRemainder s x D (1 + 2 / (n : ℝ)) z)

def blaschkeCauchyRight {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (z : ℂ) : ℂ :=
  ((3 / Real.pi : ℝ) : ℂ) *
    (blaschkeDensity s x D z * cauchyLogRight (1 + 2 / (n : ℝ)) z +
      blaschkeCauchyRemainder s x D (1 + 2 / (n : ℝ)) z)

theorem blaschkeCauchyTransform_eq_left {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) (hre : z.re < 0) :
    blaschkeCauchyTransform s x D n z = blaschkeCauchyLeft s x D n z := by
  rw [blaschkeCauchyTransform_normalized,
    integral_blaschkeCauchyKernel_eq_scalar_add_remainder s x D _ hx hz hre.ne,
    integral_cauchyConstantKernel_eq_left _ hre]
  rfl

theorem blaschkeCauchyTransform_eq_right {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z ≠ 0) (hre : 0 < z.re) :
    blaschkeCauchyTransform s x D n z = blaschkeCauchyRight s x D n z := by
  rw [blaschkeCauchyTransform_normalized,
    integral_blaschkeCauchyKernel_eq_scalar_add_remainder s x D _ hx hz hre.ne',
    integral_cauchyConstantKernel_eq_right _ hre]
  rfl

theorem blaschkeCauchyLeft_analyticAt {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) {z : ℂ} (hz : (blaschkeNodePolynomial s x).eval z ≠ 0)
    (hlo : -(1 + 2 / (n : ℝ)) < z.im) (hhi : z.im < 1 + 2 / (n : ℝ)) :
    AnalyticAt ℂ (blaschkeCauchyLeft s x D n) z := by
  unfold blaschkeCauchyLeft
  exact analyticAt_const.mul
    (((blaschkeDensity_analyticAt_of_nodePolynomial_ne_zero s x D hz).mul
      (cauchyLogLeft_analyticAt hlo hhi)).add
      (blaschkeCauchyRemainder_analyticAt s x D _ hz))

theorem blaschkeCauchyRight_analyticAt {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) {z : ℂ} (hz : (blaschkeNodePolynomial s x).eval z ≠ 0)
    (hlo : -(1 + 2 / (n : ℝ)) < z.im) (hhi : z.im < 1 + 2 / (n : ℝ)) :
    AnalyticAt ℂ (blaschkeCauchyRight s x D n) z := by
  unfold blaschkeCauchyRight
  exact analyticAt_const.mul
    (((blaschkeDensity_analyticAt_of_nodePolynomial_ne_zero s x D hz).mul
      (cauchyLogRight_analyticAt hlo hhi)).add
      (blaschkeCauchyRemainder_analyticAt s x D _ hz))

theorem blaschkeCauchyLeft_sub_right {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) {z : ℂ}
    (hlo : -(1 + 2 / (n : ℝ)) < z.im) (hhi : z.im < 1 + 2 / (n : ℝ)) :
    blaschkeCauchyLeft s x D n z - blaschkeCauchyRight s x D n z =
      6 * blaschkeDensity s x D z := by
  have hp : (Real.pi : ℂ) ≠ 0 := by
    intro h
    exact Real.pi_pos.ne' (by simpa using congrArg Complex.re h)
  have hcoeff : ((3 / Real.pi : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 6 := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    field_simp [hp]
    ring
  unfold blaschkeCauchyLeft blaschkeCauchyRight
  calc
    _ = (((3 / Real.pi : ℝ) : ℂ) *
        (cauchyLogLeft (1 + 2 / (n : ℝ)) z - cauchyLogRight (1 + 2 / (n : ℝ)) z)) *
        blaschkeDensity s x D z := by ring
    _ = _ := by rw [cauchyLogLeft_sub_cauchyLogRight hlo hhi, hcoeff]

end InternalCatalan

end



noncomputable section
namespace InternalCatalan

theorem blaschkeDensity_endpoint_difference_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx : ∀ i ∈ s, |x i| < 1)
    {c z w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1)
    (hz : ‖z - c‖ ≤ 3 / (n : ℝ)) (hw : ‖w - c‖ ≤ 3 / (n : ℝ)) :
    ‖blaschkeDensity s x D w - blaschkeDensity s x D z‖ ≤
      (4 * (n : ℝ) * Real.exp 12) * ‖w - z‖ := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hquarter : 3 / (n : ℝ) ≤ (1 / 4 : ℝ) := (div_le_iff₀ hnpos).mpr (by linarith)
  have hd : ∀ u ∈ Metric.closedBall c (3 / (n : ℝ)),
      DifferentiableAt ℂ (blaschkeDensity s x D) u := by
    intro u hu
    have hu' : ‖u - c‖ ≤ 3 / (n : ℝ) := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
    have hp : (blaschkeNodePolynomial s x).eval u ≠ 0 := by
      apply (blaschkeNodePolynomial_eval_ne_zero_iff s x u).mpr
      intro i hi
      apply sub_ne_zero.mp
      exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num)
        (blaschkeFactor_endpoint_norm_lower (hx i hi) hc hci (hu'.trans hquarter)).1)
    exact (blaschkeDensity_analyticAt_of_nodePolynomial_ne_zero s x D hp).differentiableAt
  have hb : ∀ u ∈ Metric.closedBall c (3 / (n : ℝ)),
      ‖deriv (blaschkeDensity s x D) u‖ ≤ 4 * (n : ℝ) * Real.exp 12 := by
    intro u hu
    exact blaschkeDensity_endpoint_deriv_norm_le s x D n hn hD hcard hx hc hci
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu)
  exact Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_closedBall c _)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw)

theorem blaschkeDensity_endpoint_difference_quotient_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx : ∀ i ∈ s, |x i| < 1)
    {c z w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1)
    (hz : ‖z - c‖ ≤ 3 / (n : ℝ)) (hw : ‖w - c‖ ≤ 3 / (n : ℝ)) :
    ‖(blaschkeDensity s x D w - blaschkeDensity s x D z) / (w - z)‖ ≤
      4 * (n : ℝ) * Real.exp 12 := by
  by_cases heq : w = z
  · simp only [heq, sub_self, zero_div, norm_zero]
    positivity
  · rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr heq))).mpr
    exact blaschkeDensity_endpoint_difference_norm_le s x D n hn hD hcard hx hc hci hz hw

end InternalCatalan




open MeasureTheory Polynomial
open scoped Interval
namespace InternalCatalan

def blaschkeInterpolant {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (z : ℂ) : ℂ :=
  z ^ D - ((3 / Real.pi : ℝ) : ℂ) *
    (z ^ D * (cauchyLogLeft (1 + 2 / (n : ℝ)) z -
      blaschkeIntegratedDividedDifference s x (1 + 2 / (n : ℝ)) (blaschkeNodePolynomial s x) z) +
    finiteBlaschke s x z *
      blaschkeIntegratedDividedDifference s x (1 + 2 / (n : ℝ)) (blaschkeDensityNumerator s x D) z)

theorem blaschkeNodePolynomial_eval_node {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {i : ι} (hi : i ∈ s) : (blaschkeNodePolynomial s x).eval (x i : ℂ) = 0 := by
  by_contra h
  exact ((blaschkeNodePolynomial_eval_ne_zero_iff s x _).mp h i hi) rfl

theorem blaschkeIntegratedNodeDifference_eq_scalarIntegral {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (T : ℝ) (hx : ∀ i ∈ s, x i ≠ 0) {z : ℂ}
    (hz : (blaschkeNodePolynomial s x).eval z = 0) (hre : z.re ≠ 0) :
    blaschkeIntegratedDividedDifference s x T (blaschkeNodePolynomial s x) z =
      ∫ t in -T..T, (1 : ℂ) / (Complex.I * (t : ℂ) - z) := by
  rw [← integral_blaschkeDividedDifference_quotient s x hx]
  apply intervalIntegral.integral_congr
  intro t _
  have hid := sub_mul_polynomialDividedDifference (blaschkeNodePolynomial s x) z
    (Complex.I * (t : ℂ))
  rw [hz, sub_zero] at hid
  apply (div_eq_div_iff (blaschkeNodePolynomial_eval_imaginary_ne_zero s x hx t)
    (imaginary_sub_ne_zero_of_re_ne_zero hre t)).mpr
  simpa only [one_mul, mul_comm] using hid

theorem blaschkeInterpolant_analyticAt {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) {z : ℂ} (hden : ∀ i ∈ s, 1 - (x i : ℂ) * z ≠ 0)
    (hlo : -(1 + 2 / (n : ℝ)) < z.im) (hhi : z.im < 1 + 2 / (n : ℝ)) :
    AnalyticAt ℂ (blaschkeInterpolant s x D n) z := by
  unfold blaschkeInterpolant
  exact (analyticAt_id.pow D).sub (analyticAt_const.mul
    (((analyticAt_id.pow D).mul ((cauchyLogLeft_analyticAt hlo hhi).sub
      (blaschkeIntegratedDividedDifference_analyticAt _ _ _ _ _))).add
      ((finiteBlaschke_analyticAt s x hden).mul
        (blaschkeIntegratedDividedDifference_analyticAt _ _ _ _ _))))

theorem blaschkeInterpolant_analyticOnNhd_closedDisk {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hn : 0 < n) (hx : ∀ i ∈ s, |x i| < 1) :
    AnalyticOnNhd ℂ (blaschkeInterpolant s x D n) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  have hzn : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have him : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hzn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrad : 1 < 1 + 2 / (n : ℝ) := by
    have hpos : (0 : ℝ) < 2 / (n : ℝ) := div_pos (by norm_num) hnR
    linarith
  have hstrip : |z.im| < 1 + 2 / (n : ℝ) := him.trans_lt hrad
  exact blaschkeInterpolant_analyticAt s x D n
    (fun i hi => blaschkeFactor_denominator_ne_zero (hx i hi) hzn)
    (abs_lt.mp hstrip).1 (abs_lt.mp hstrip).2

theorem blaschkeInterpolant_eval_negative_node {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {i : ι}
    (hi : i ∈ s) (hneg : x i < 0) :
    blaschkeInterpolant s x D n (x i : ℂ) = (x i : ℂ) ^ D := by
  have hre : (x i : ℂ).re < 0 := hneg
  have hUP := blaschkeIntegratedNodeDifference_eq_scalarIntegral s x (1 + 2 / (n : ℝ)) hx
    (blaschkeNodePolynomial_eval_node s x hi) hre.ne
  rw [integral_cauchyConstantKernel_eq_left _ hre] at hUP
  unfold blaschkeInterpolant
  rw [hUP, sub_self, finiteBlaschke_eval_node s x hi]
  ring

private theorem cauchy_coefficient_mul_two_pi :
    ((3 / Real.pi : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 6 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by
    intro h
    exact Real.pi_pos.ne' (by simpa using congrArg Complex.re h)
  rw [Complex.ofReal_div, Complex.ofReal_ofNat]
  field_simp [hp]
  ring

theorem blaschkeInterpolant_eval_positive_node {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) (hx : ∀ i ∈ s, x i ≠ 0) {i : ι}
    (hi : i ∈ s) (hpos : 0 < x i) :
    blaschkeInterpolant s x D n (x i : ℂ) = -5 * (x i : ℂ) ^ D := by
  have hre : 0 < (x i : ℂ).re := hpos
  have hUP := blaschkeIntegratedNodeDifference_eq_scalarIntegral s x (1 + 2 / (n : ℝ)) hx
    (blaschkeNodePolynomial_eval_node s x hi) hre.ne'
  rw [integral_cauchyConstantKernel_eq_right _ hre] at hUP
  have hrad : (0 : ℝ) < 1 + 2 / (n : ℝ) := by positivity
  have hlo : -(1 + 2 / (n : ℝ)) < (x i : ℂ).im := by simpa only [Complex.ofReal_im] using (neg_lt_zero.mpr hrad)
  have hhi : (x i : ℂ).im < 1 + 2 / (n : ℝ) := by simpa using hrad
  unfold blaschkeInterpolant
  rw [hUP, cauchyLogLeft_sub_cauchyLogRight hlo hhi, finiteBlaschke_eval_node s x hi]
  calc
    _ = (x i : ℂ) ^ D -
        (((3 / Real.pi : ℝ) : ℂ) * (2 * (Real.pi : ℂ))) * (x i : ℂ) ^ D := by ring
    _ = -5 * (x i : ℂ) ^ D := by rw [cauchy_coefficient_mul_two_pi]; ring

theorem blaschkeInterpolant_eq_left_continuation {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) {z : ℂ} (hB : finiteBlaschke s x z ≠ 0) :
    blaschkeInterpolant s x D n z = z ^ D - finiteBlaschke s x z * blaschkeCauchyLeft s x D n z := by
  have hBF : finiteBlaschke s x z * blaschkeDensity s x D z = z ^ D := by
    unfold blaschkeDensity
    field_simp [hB]
  unfold blaschkeInterpolant blaschkeCauchyLeft blaschkeCauchyRemainder
  rw [← blaschkeDensity_eq_eval_div]
  calc
    _ = z ^ D - ((3 / Real.pi : ℝ) : ℂ) *
        ((finiteBlaschke s x z * blaschkeDensity s x D z) *
          (cauchyLogLeft (1 + 2 / (n : ℝ)) z -
            blaschkeIntegratedDividedDifference s x (1 + 2 / (n : ℝ)) (blaschkeNodePolynomial s x) z) +
        finiteBlaschke s x z *
          blaschkeIntegratedDividedDifference s x (1 + 2 / (n : ℝ)) (blaschkeDensityNumerator s x D) z) := by
            rw [hBF]
    _ = _ := by ring

theorem blaschkeInterpolant_eq_right_continuation {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (D n : ℕ) {z : ℂ} (hB : finiteBlaschke s x z ≠ 0)
    (hlo : -(1 + 2 / (n : ℝ)) < z.im) (hhi : z.im < 1 + 2 / (n : ℝ)) :
    blaschkeInterpolant s x D n z = -5 * z ^ D - finiteBlaschke s x z * blaschkeCauchyRight s x D n z := by
  have hBF : finiteBlaschke s x z * blaschkeDensity s x D z = z ^ D := by
    unfold blaschkeDensity
    field_simp [hB]
  have hj := blaschkeCauchyLeft_sub_right s x D n hlo hhi
  have heq : blaschkeCauchyLeft s x D n z =
      6 * blaschkeDensity s x D z + blaschkeCauchyRight s x D n z :=
    (sub_eq_iff_eq_add).mp hj
  rw [blaschkeInterpolant_eq_left_continuation s x D n hB, heq]
  calc
    _ = -5 * z ^ D - finiteBlaschke s x z * blaschkeCauchyRight s x D n z +
        6 * (z ^ D - finiteBlaschke s x z * blaschkeDensity s x D z) := by ring
    _ = _ := by rw [hBF]; ring

end InternalCatalan

end



noncomputable section
namespace InternalCatalan

theorem blaschkeNodePolynomial_ne_zero_on_circle {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    (blaschkeNodePolynomial s x).eval z ≠ 0 := by
  apply (blaschkeNodePolynomial_eval_ne_zero_iff s x z).mpr
  intro i hi heq
  have hh := congrArg (fun w : ℂ => ‖w‖) heq
  rw [hz, Complex.norm_real, Real.norm_eq_abs] at hh
  exact (ne_of_lt (hx i hi)) hh.symm

theorem blaschkeDensity_norm_eq_one_on_circle {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (hx : ∀ i ∈ s, |x i| < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖blaschkeDensity s x D z‖ = 1 := by
  unfold blaschkeDensity
  rw [norm_div, norm_pow, hz, one_pow, finiteBlaschke_norm_eq_one s x hx hz, div_one]

private theorem circle_inside_cauchy_strip (n : ℕ) (hn : 0 < n) {z : ℂ} (hz : ‖z‖ = 1) :
    |z.im| < 1 + 2 / (n : ℝ) := by
  have hh : |z.im| ≤ 1 := by simpa only [hz] using Complex.abs_im_le_norm z
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : (0 : ℝ) < 2 / (n : ℝ) := div_pos (by norm_num) hnR
  linarith

theorem blaschkeInterpolant_circle_eq_left {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re < 0) :
    blaschkeInterpolant s x D n z = z ^ D - finiteBlaschke s x z * blaschkeCauchyTransform s x D n z := by
  have hB : finiteBlaschke s x z ≠ 0 := norm_pos_iff.mp
    (by rw [finiteBlaschke_norm_eq_one s x hx hz]; norm_num)
  rw [blaschkeInterpolant_eq_left_continuation s x D n hB,
    blaschkeCauchyTransform_eq_left s x D n hx0 (blaschkeNodePolynomial_ne_zero_on_circle s x hx hz) hre]

theorem blaschkeInterpolant_circle_eq_right {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hn : 0 < n) (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hre : 0 < z.re) :
    blaschkeInterpolant s x D n z = -5 * z ^ D - finiteBlaschke s x z * blaschkeCauchyTransform s x D n z := by
  have hB : finiteBlaschke s x z ≠ 0 := norm_pos_iff.mp
    (by rw [finiteBlaschke_norm_eq_one s x hx hz]; norm_num)
  have hs := abs_lt.mp (circle_inside_cauchy_strip n hn hz)
  rw [blaschkeInterpolant_eq_right_continuation s x D n hB hs.1 hs.2,
    blaschkeCauchyTransform_eq_right s x D n hx0 (blaschkeNodePolynomial_ne_zero_on_circle s x hx hz) hre]

theorem blaschkeInterpolant_circle_norm_le_five_add {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hn : 0 < n) (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0) :
    ‖blaschkeInterpolant s x D n z‖ ≤ 5 + ‖blaschkeCauchyTransform s x D n z‖ := by
  have hB := finiteBlaschke_norm_eq_one s x hx hz
  rcases lt_or_gt_of_ne hre with hre | hre
  · rw [blaschkeInterpolant_circle_eq_left s x D n hx0 hx hz hre]
    have hh := norm_sub_le (z ^ D) (finiteBlaschke s x z * blaschkeCauchyTransform s x D n z)
    simp only [norm_pow, hz, one_pow, norm_mul, hB, one_mul] at hh
    linarith
  · rw [blaschkeInterpolant_circle_eq_right s x D n hn hx0 hx hz hre]
    have hh := norm_sub_le (-5 * z ^ D) (finiteBlaschke s x z * blaschkeCauchyTransform s x D n z)
    simpa [norm_mul, norm_pow, hz, hB] using hh

theorem interpolant_far_axis_numerical (n : ℕ) (hn : 48 ≤ n) :
    5 + 30 * Real.exp 2 * (n : ℝ) ≤ 10 * Real.exp 12 * (n : ℝ) := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hE : 1 ≤ Real.exp 12 := Real.one_le_exp (by norm_num)
  have hten : 11 ≤ Real.exp 10 := by linarith [Real.add_one_le_exp 10]
  have heq : Real.exp 12 = Real.exp 2 * Real.exp 10 := by rw [← Real.exp_add]; norm_num
  have hratio : 11 * Real.exp 2 ≤ Real.exp 12 := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hten (Real.exp_pos 2).le]
  have hratio' : 30 * Real.exp 2 ≤ 3 * Real.exp 12 := by nlinarith [Real.exp_pos 2]
  have hrn := mul_le_mul_of_nonneg_right hratio' (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hEn := mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

theorem interpolant_near_axis_numerical (n : ℕ) (hn : 48 ≤ n) :
    5 + (6 * Real.exp 2 * (n : ℝ) + 12 * Real.exp 12 + 3 * (n : ℝ)) ≤
      10 * Real.exp 12 * (n : ℝ) := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hE : 1 ≤ Real.exp 12 := Real.one_le_exp (by norm_num)
  have h2 : Real.exp 2 ≤ Real.exp 12 := Real.exp_le_exp.mpr (by norm_num)
  have h2n := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hEn := mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have h17n : 17 * Real.exp 12 ≤ (n : ℝ) * Real.exp 12 :=
    mul_le_mul_of_nonneg_right (by linarith : (17 : ℝ) ≤ n) (Real.exp_pos 12).le
  nlinarith

end InternalCatalan




open MeasureTheory Set
open scoped BigOperators Interval
namespace InternalCatalan

theorem blaschkeCauchyKernel_local_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx0 : ∀ i ∈ s, x i ≠ 0)
    (hx : ∀ i ∈ s, |x i| < 1) (a b : ℝ) (hab : a ≤ b)
    (hlen : b - a ≤ 3 / (n : ℝ)) {c z : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hz : ‖z‖ = 1) (hre : z.re ≠ 0)
    (hzc : ‖z - c‖ ≤ 3 / (n : ℝ))
    (hpath : ∀ t ∈ Icc a b, ‖Complex.I * (t : ℂ) - c‖ ≤ 3 / (n : ℝ))
    (hal : 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (a : ℂ) - z‖)
    (hau : ‖Complex.I * (a : ℂ) - z‖ ≤ 1)
    (hbl : 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (b : ℂ) - z‖)
    (hbu : ‖Complex.I * (b : ℂ) - z‖ ≤ 1) :
    ‖∫ t in a..b, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)‖ ≤ 12 * Real.exp 12 + 3 * (n : ℝ) := by
  let g : ℝ → ℂ := fun t =>
    (blaschkeDensity s x D (Complex.I * (t : ℂ)) - blaschkeDensity s x D z) /
      (Complex.I * (t : ℂ) - z)
  have hgc : Continuous g :=
    ((continuous_blaschkeDensity_imaginary s x D hx0).sub continuous_const).div
      ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const)
      (imaginary_sub_ne_zero_of_re_ne_zero hre)
  have hgi : IntervalIntegrable g volume a b := hgc.intervalIntegrable _ _
  have hsc : IntervalIntegrable (fun t : ℝ => blaschkeDensity s x D z *
      (1 / (Complex.I * (t : ℂ) - z))) volume a b :=
    (intervalIntegrable_cauchyConstantKernel_interval a b hre).const_mul _
  have hfun : (fun t : ℝ => blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)) =
      (fun t : ℝ => g t + blaschkeDensity s x D z * (1 / (Complex.I * (t : ℂ) - z))) := by
    funext t
    dsimp only [g]
    ring
  have hgb : ‖∫ t in a..b, g t‖ ≤ 12 * Real.exp 12 := by
    have hi : ‖∫ t in a..b, g t‖ ≤ (4 * (n : ℝ) * Real.exp 12) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hab] at ht
      exact blaschkeDensity_endpoint_difference_quotient_norm_le s x D n hn hD hcard hx
        hc hci hzc (hpath t ⟨ht.1.le, ht.2⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
    have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 48) hn)
    calc
      _ ≤ (4 * (n : ℝ) * Real.exp 12) * (b - a) := hi
      _ ≤ (4 * (n : ℝ) * Real.exp 12) * (3 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = 12 * Real.exp 12 := by field_simp [hnR.ne']; ring
  rw [hfun, intervalIntegral.integral_add hgi hsc, intervalIntegral.integral_const_mul]
  calc
    _ ≤ ‖∫ t in a..b, g t‖ +
        ‖blaschkeDensity s x D z * (∫ t in a..b, (1 : ℂ) / (Complex.I * (t : ℂ) - z))‖ := norm_add_le _ _
    _ ≤ 12 * Real.exp 12 + 3 * (n : ℝ) := by
      rw [norm_mul, blaschkeDensity_norm_eq_one_on_circle s x D hx hz, one_mul]
      exact add_le_add hgb (cauchyConstantKernel_interval_norm_le_three_mul n hn a b hre hal hau hbl hbu)

theorem blaschkeCauchyKernel_far_piece_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hx : ∀ i ∈ s, x i ^ 2 ≤ 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    (a b : ℝ) (hab : a ≤ b) (hlen : b - a ≤ 3) {z : ℂ}
    (hpath : ∀ t ∈ Icc a b, |t| ≤ 1 + 2 / (n : ℝ))
    (hsep : ∀ t ∈ Icc a b, 1 / (2 * (n : ℝ)) ≤ ‖Complex.I * (t : ℂ) - z‖) :
    ‖∫ t in a..b, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)‖ ≤ 6 * Real.exp 2 * (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 48) hn)
  have hi : ‖∫ t in a..b, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
      (Complex.I * (t : ℂ) - z)‖ ≤ (2 * Real.exp 2 * (n : ℝ)) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le hab] at ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    have hp : (0 : ℝ) < ‖Complex.I * (t : ℂ) - z‖ :=
      lt_of_lt_of_le (by positivity) (hsep t ht')
    have hF : ‖blaschkeDensity s x D (Complex.I * (t : ℂ))‖ ≤ Real.exp 2 :=
      finiteBlaschke_diameter_quotient_le_exp_two s x D n hDpos hD hx hweight (hpath t ht')
    rw [norm_div]
    apply (div_le_iff₀ hp).mpr
    have hs := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))).mp (hsep t ht')
    have hm := mul_le_mul_of_nonneg_left hs (Real.exp_pos 2).le
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  calc
    _ ≤ (2 * Real.exp 2 * (n : ℝ)) * (b - a) := hi
    _ ≤ (2 * Real.exp 2 * (n : ℝ)) * 3 := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = 6 * Real.exp 2 * (n : ℝ) := by ring

end InternalCatalan

end



noncomputable section
open MeasureTheory Set
open scoped BigOperators Interval
namespace InternalCatalan

theorem blaschkeCauchyTransform_norm_le_split {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D n : ℕ) (hx0 : ∀ i ∈ s, x i ≠ 0) {z : ℂ} (hre : z.re ≠ 0) (a : ℝ) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      ‖∫ t in -(1 + 2 / (n : ℝ))..a, blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)‖ +
      ‖∫ t in a..(1 + 2 / (n : ℝ)), blaschkeDensity s x D (Complex.I * (t : ℂ)) /
        (Complex.I * (t : ℂ) - z)‖ := by
  have hc := continuous_blaschkeCauchyKernel s x D hx0 hre
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-(1 + 2 / (n : ℝ))) a)
    (hc.intervalIntegrable a (1 + 2 / (n : ℝ)))
  have hcoeff : ‖((3 / Real.pi : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  rw [blaschkeCauchyTransform_normalized, norm_mul, ← hi]
  calc
    _ ≤ 1 * ‖(∫ t in -(1 + 2 / (n : ℝ))..a,
        blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)) +
        (∫ t in a..(1 + 2 / (n : ℝ)),
          blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z))‖ :=
      mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ ≤ _ := by
      simpa only [one_mul] using
        (norm_add_le
          (∫ t in -(1 + 2 / (n : ℝ))..a,
            blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z))
          (∫ t in a..(1 + 2 / (n : ℝ)),
            blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)))

theorem blaschkeCauchyTransform_upper_crossing_bound {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0)
    (hnear : |z.re| ≤ 1 / (10 * (n : ℝ))) (him : 0 ≤ z.im) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      6 * Real.exp 2 * (n : ℝ) + 12 * Real.exp 12 + 3 * (n : ℝ) := by
  let r : ℝ := 1 / (n : ℝ)
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : r ≤ (1 / 48 : ℝ) := by
    dsimp only [r]
    apply (div_le_iff₀ hnpos).mpr
    linarith
  have hT : 1 + 2 / (n : ℝ) = 1 + 2 * r := by dsimp [r]; ring
  have h3 : 3 / (n : ℝ) = 3 * r := by dsimp [r]; ring
  have hhalf : 1 / (2 * (n : ℝ)) = r / 2 := by dsimp [r]; field_simp [hnpos.ne']
  have hnear' : |z.re| ≤ r / 10 := by
    convert! hnear using 1
    dsimp [r]
    field_simp [hnpos.ne']
  have hloc := upper_circle_crossing_location hz him hnear'
  have hend := upper_crossing_endpoint_distances hr hrsmall hz him hnear'
  have hsq : ∀ i ∈ s, x i ^ 2 ≤ 1 := by
    intro i hi
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (x i)) (hx i hi).le 2
  have hlocal : ‖∫ t in (1 - r)..(1 + 2 * r),
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      12 * Real.exp 12 + 3 * (n : ℝ) := by
    apply blaschkeCauchyKernel_local_norm_le s x D n hn hD hcard hx0 hx
      (1 - r) (1 + 2 * r) (by linarith) (by rw [h3]; linarith)
      (c := Complex.I) (by simp) (by simp) hz hre
    · rw [h3]; linarith [hloc.2.2]
    · intro t ht
      rw [h3]
      exact (upper_crossing_local_path hr ht.1 ht.2).trans (by linarith)
    · rw [hhalf]; exact hend.1.1
    · exact hend.1.2
    · rw [hhalf]; exact hend.2.1
    · exact hend.2.2
  have hfar : ‖∫ t in -(1 + 2 * r)..(1 - r),
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      6 * Real.exp 2 * (n : ℝ) := by
    apply blaschkeCauchyKernel_far_piece_norm_le s x D n hn hDpos hD hsq hweight
      (-(1 + 2 * r)) (1 - r) (by linarith) (by linarith)
    · intro t ht
      rw [hT]
      exact abs_le.mpr ⟨ht.1, by linarith [ht.2]⟩
    · intro t ht
      rw [hhalf]
      exact upper_crossing_far_separation hr hloc.1 ht.2
  have hsplit := blaschkeCauchyTransform_norm_le_split s x D n hx0 hre (1 - r)
  rw [hT] at hsplit
  linarith

theorem blaschkeCauchyTransform_lower_crossing_bound {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0)
    (hnear : |z.re| ≤ 1 / (10 * (n : ℝ))) (him : z.im ≤ 0) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      6 * Real.exp 2 * (n : ℝ) + 12 * Real.exp 12 + 3 * (n : ℝ) := by
  let r : ℝ := 1 / (n : ℝ)
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : r ≤ (1 / 48 : ℝ) := by
    dsimp only [r]
    apply (div_le_iff₀ hnpos).mpr
    linarith
  have hT : 1 + 2 / (n : ℝ) = 1 + 2 * r := by dsimp [r]; ring
  have h3 : 3 / (n : ℝ) = 3 * r := by dsimp [r]; ring
  have hhalf : 1 / (2 * (n : ℝ)) = r / 2 := by dsimp [r]; field_simp [hnpos.ne']
  have hnear' : |z.re| ≤ r / 10 := by
    convert! hnear using 1
    dsimp [r]
    field_simp [hnpos.ne']
  have hloc := lower_circle_crossing_location hz him hnear'
  have hend := lower_crossing_endpoint_distances hr hrsmall hz him hnear'
  have hsq : ∀ i ∈ s, x i ^ 2 ≤ 1 := by
    intro i hi
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (x i)) (hx i hi).le 2
  have hlocal : ‖∫ t in -(1 + 2 * r)..(-1 + r),
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      12 * Real.exp 12 + 3 * (n : ℝ) := by
    rw [show -(1 + 2 * r) = -1 - 2 * r by ring]
    apply blaschkeCauchyKernel_local_norm_le s x D n hn hD hcard hx0 hx
      (-1 - 2 * r) (-1 + r) (by linarith) (by rw [h3]; linarith)
      (c := -Complex.I) (by simp) (by simp) hz hre
    · rw [sub_neg_eq_add, h3]; linarith [hloc.2.2]
    · intro t ht
      rw [sub_neg_eq_add, h3]
      exact (lower_crossing_local_path hr ht.1 ht.2).trans (by linarith)
    · rw [hhalf]; exact hend.1.1
    · exact hend.1.2
    · rw [hhalf]; exact hend.2.1
    · exact hend.2.2
  have hfar : ‖∫ t in (-1 + r)..(1 + 2 * r),
      blaschkeDensity s x D (Complex.I * (t : ℂ)) / (Complex.I * (t : ℂ) - z)‖ ≤
      6 * Real.exp 2 * (n : ℝ) := by
    apply blaschkeCauchyKernel_far_piece_norm_le s x D n hn hDpos hD hsq hweight
      (-1 + r) (1 + 2 * r) (by linarith) (by linarith)
    · intro t ht
      rw [hT]
      exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    · intro t ht
      rw [hhalf]
      exact lower_crossing_far_separation hr hloc.2.1 ht.1
  have hsplit := blaschkeCauchyTransform_norm_le_split s x D n hx0 hre (-1 + r)
  rw [hT] at hsplit
  linarith

theorem blaschkeCauchyTransform_near_axis_bound {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0) (hnear : |z.re| ≤ 1 / (10 * (n : ℝ))) :
    ‖blaschkeCauchyTransform s x D n z‖ ≤
      6 * Real.exp 2 * (n : ℝ) + 12 * Real.exp 12 + 3 * (n : ℝ) := by
  rcases le_total 0 z.im with him | him
  · exact blaschkeCauchyTransform_upper_crossing_bound s x D n hn hDpos hD hcard hx0 hx hweight hz hre hnear him
  · exact blaschkeCauchyTransform_lower_crossing_bound s x D n hn hDpos hD hcard hx0 hx hweight hz hre hnear him

end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan

theorem blaschkeInterpolant_boundary_norm_le_off_axis {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re ≠ 0) :
    ‖blaschkeInterpolant s x D n z‖ ≤ 10 * Real.exp 12 * (n : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase := blaschkeInterpolant_circle_norm_le_five_add s x D n hn0 hx0 hx hz hre
  by_cases hfar : 1 / (10 * (n : ℝ)) ≤ |z.re|
  · have hsq : ∀ i ∈ s, x i ^ 2 ≤ 1 := by
      intro i hi
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (x i)) (hx i hi).le 2
    exact (hbase.trans (add_le_add (le_refl 5)
      (blaschkeCauchyTransform_far_axis_bound s x D n hn hDpos hD hsq hweight hfar))).trans
      (interpolant_far_axis_numerical n hn)
  · have hnear : |z.re| ≤ 1 / (10 * (n : ℝ)) := (lt_of_not_ge hfar).le
    exact (hbase.trans (add_le_add (le_refl 5)
      (blaschkeCauchyTransform_near_axis_bound s x D n hn hDpos hD hcard hx0 hx hweight hz hre hnear))).trans
      (interpolant_near_axis_numerical n hn)

end InternalCatalan

end



noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace InternalCatalan

theorem blaschkeInterpolant_boundary_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖blaschkeInterpolant s x D n z‖ ≤ 10 * Real.exp 12 * (n : ℝ) := by
  by_cases hre : z.re ≠ 0
  · exact blaschkeInterpolant_boundary_norm_le_off_axis s x D n hn hDpos hD hcard hx0 hx hweight hz hre
  have hre0 : z.re = 0 := not_ne_iff.mp hre
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hA := blaschkeInterpolant_analyticOnNhd_closedDisk s x D n hn0 hx
  have hzclosed : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, hz, le_refl]
  have hcont : ContinuousAt (fun w : ℂ => ‖blaschkeInterpolant s x D n w‖) z :=
    (hA z hzclosed).continuousAt.norm
  have hcomp : ContinuousAt (fun t : ℝ =>
      ‖blaschkeInterpolant s x D n (circleRightPerturb z t)‖) 0 := by
    simpa only [Function.comp_def] using hcont.comp_of_eq
      (f := circleRightPerturb z) (circleRightPerturb_continuousAt_zero hz) (circleRightPerturb_zero hz)
  have ht : Tendsto (fun t : ℝ => ‖blaschkeInterpolant s x D n (circleRightPerturb z t)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖blaschkeInterpolant s x D n z‖) := by
    simpa only [circleRightPerturb_zero hz] using
      hcomp.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply le_of_tendsto ht
  exact (show ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi 0 from self_mem_nhdsWithin).mono (fun t ht => by
    have hp := circleRightPerturb_norm_and_re hre0 ht
    exact blaschkeInterpolant_boundary_norm_le_off_axis s x D n hn hDpos hD hcard hx0 hx hweight hp.1 hp.2)

theorem blaschkeInterpolant_closedDisk_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖blaschkeInterpolant s x D n z‖ ≤ 10 * Real.exp 12 * (n : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hA := blaschkeInterpolant_analyticOnNhd_closedDisk s x D n hn0 hx
  have hd : DiffContOnCl ℂ (blaschkeInterpolant s x D n) (Metric.ball (0 : ℂ) 1) :=
    hA.differentiableOn.diffContOnCl_ball Set.Subset.rfl
  refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd ?_ ?_
  · intro w hw
    apply blaschkeInterpolant_boundary_norm_le s x D n hn hDpos hD hcard hx0 hx hweight
    simpa only [frontier_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0),
      Metric.mem_sphere, dist_zero_right] using hw
  · simpa only [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)] using hz

theorem real_uniform_interpolation_actual {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hDpos : 0 < D) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx0 : ∀ i ∈ s, x i ≠ 0) (hx : ∀ i ∈ s, |x i| < 1)
    (hweight : (∑ i ∈ s, blaschkeWeight (x i)) ≤ (D : ℝ)) :
    ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ i ∈ s, h (x i : ℂ) = if x i < 0 then (x i : ℂ) ^ D else -5 * (x i : ℂ) ^ D) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h z‖ ≤ 10 * Real.exp 12 * (n : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  refine ⟨blaschkeInterpolant s x D n,
    blaschkeInterpolant_analyticOnNhd_closedDisk s x D n hn0 hx, ?_, ?_⟩
  · intro i hi
    by_cases hneg : x i < 0
    · rw [ite_eq_left hneg]
      exact blaschkeInterpolant_eval_negative_node s x D n hx0 hi hneg
    · rw [ite_eq_right hneg]
      exact blaschkeInterpolant_eval_positive_node s x D n hx0 hi
        ((lt_or_gt_of_ne (hx0 i hi)).resolve_left hneg)
  · intro z hz
    exact blaschkeInterpolant_closedDisk_norm_le s x D n hn hDpos hD hcard hx0 hx hweight hz

end InternalCatalan

end

end OAI
