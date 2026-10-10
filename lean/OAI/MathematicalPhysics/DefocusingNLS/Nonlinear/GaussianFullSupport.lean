import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianRealization
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianSmallBalls

namespace OAI

/-!
# Full support of the Fourier Gaussian law

The small-tail/independent-head estimate is converted to positive mass of
all Hilbert balls, and hence all nonempty open Sobolev sets.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DefocusingNLS

lemma ofReal_norm_sub_sq_le (x y : ℂ) :
    ENNReal.ofReal (‖x - y‖ ^ 2) ≤
      2 * ENNReal.ofReal (‖x‖ ^ 2) + 2 * ENNReal.ofReal (‖y‖ ^ 2) := by
  have h : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have ht := norm_sub_le x y
    have hp := sq_nonneg (‖x‖ - ‖y‖)
    nlinarith [norm_nonneg (x - y), norm_nonneg x, norm_nonneg y]
  calc
    _ ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      norm_num

lemma sqrt_weight_norm_sq (w : ℝ) (hw : 0 ≤ w) (z : ℂ) :
    ‖(Real.sqrt w : ℂ) * z‖ ^ 2 = w * Complex.normSq z := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg w), Real.sq_sqrt hw, Complex.sq_norm]

section CountableProduct

variable {ι : Type*} [Countable ι]

/-- All squared-error balls about square-summable coefficient vectors have
positive probability under a positive square-summable Gaussian weighting. -/
theorem gaussian_error_energy_pos (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hwsum : Summable w) (f : ι → ℂ) (hfsum : Summable (fun i => ‖f i‖ ^ 2))
    {r : ℝ} (hr : 0 < r) :
    0 < Measure.infinitePi (fun _ : ι => complexGaussian (1 / 2))
      {g | (∑' i, ENNReal.ofReal (‖(Real.sqrt (w i) : ℂ) * g i - f i‖ ^ 2)) <
        ENNReal.ofReal r} := by
  classical
  have hsmall : 0 < ENNReal.ofReal (r / 8) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨S, hwS, hfS⟩ := exists_small_variance_target_tails w hwsum f hfsum hsmall
  have hpos := gaussian_head_and_tail_pos w hw S f (δ := r / 2) (by positivity) hwS
  refine lt_of_lt_of_le hpos (measure_mono ?_)
  intro g hg
  change (∑' i, ENNReal.ofReal (‖(Real.sqrt (w i) : ℂ) * g i - f i‖ ^ 2)) <
    ENNReal.ofReal r
  have hhead : (∑ i ∈ S,
      ENNReal.ofReal (‖(Real.sqrt (w i) : ℂ) * g i - f i‖ ^ 2)) <
      ENNReal.ofReal (r / 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro i hi; positivity)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have hh := hg.1
    change (∑ i : S, ‖(Real.sqrt (w i) : ℂ) * g i - f i‖ ^ 2) < r / 2 at hh
    rw [Finset.sum_coe_sort S (fun i : ι => ‖(Real.sqrt (w i) : ℂ) * g i - f i‖ ^ 2)] at hh
    exact hh
  have htail : (∑' i : ↥((S : Set ι)ᶜ),
      ENNReal.ofReal (‖(Real.sqrt (w i) : ℂ) * g i - f i‖ ^ 2)) ≤
      2 * gaussianTailEnergy w S g +
        2 * (∑' i : ↥((S : Set ι)ᶜ), ENNReal.ofReal (‖f i‖ ^ 2)) := by
    calc
      _ ≤ ∑' i : ↥((S : Set ι)ᶜ),
          (2 * (ENNReal.ofReal (w i) * ENNReal.ofReal (Complex.normSq (g i))) +
            2 * ENNReal.ofReal (‖f i‖ ^ 2)) := by
        apply ENNReal.tsum_le_tsum
        intro i
        simpa only [sqrt_weight_norm_sq _ (hw i).le,
          ENNReal.ofReal_mul (hw i).le] using
          ofReal_norm_sub_sq_le ((Real.sqrt (w i) : ℂ) * g i) (f i)
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]; rfl
  have hstrict : (∑' i, ENNReal.ofReal (‖(Real.sqrt (w i) : ℂ) * g i - f i‖ ^ 2)) <
      ENNReal.ofReal (r / 2) +
        (2 * ENNReal.ofReal (r / 8) + 2 * ENNReal.ofReal (r / 8)) := by
    rw [← ENNReal.sum_add_tsum_compl S]
    refine lt_of_le_of_lt (add_le_add le_rfl htail) ?_
    exact ENNReal.add_lt_add hhead (ENNReal.add_lt_add
      (ENNReal.mul_lt_mul_right (by norm_num) (by simp) hg.2)
      (ENNReal.mul_lt_mul_right (by norm_num) (by simp) hfS))
  have hscale : (2 : ℝ≥0∞) * ENNReal.ofReal (r / 8) = ENNReal.ofReal (r / 4) := by
    have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
    rw [← htwo, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hscale, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hstrict
  simpa only [show r / 2 + (r / 4 + r / 4) = r by ring] using hstrict

end CountableProduct

/-- Every Hilbert ball has positive probability for the Gaussian Fourier law at
exactly the manuscript's Sobolev threshold. -/
theorem weightedGaussianLaw_ball_pos (k α : ℝ) (hα : k + 6 < α)
    (f : FourierL2) {r : ℝ} (hr : 0 < r) :
    0 < weightedGaussianLaw k α (Metric.ball f r) := by
  have hw : ∀ n, 0 < sobolevVariance k α n := by
    intro n
    exact Real.rpow_pos_of_pos (by positivity) _
  have hf : Summable (fun n => ‖f n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := 2) (by norm_num) f).summable
  have hpos := gaussian_error_energy_pos (sobolevVariance k α) hw
    (summable_sobolev_variances k α hα) (fun n => f n) hf (sq_pos_of_pos hr)
  change 0 < fourierGaussianLaw _ at hpos
  rw [weightedGaussianLaw, Measure.map_apply (measurable_weightedGaussianVector k α)
    Metric.isOpen_ball.measurableSet]
  refine lt_of_lt_of_le hpos (measure_mono_ae ?_)
  filter_upwards [ae_weightedGaussianVector_coefficients k α hα] with g hg herror
  change dist (weightedGaussianVector k α g) f < r
  rw [dist_eq_norm]
  have hnorm : ENNReal.ofReal (‖weightedGaussianVector k α g - f‖ ^ 2) =
      ∑' n, ENNReal.ofReal
        (‖(Real.sqrt (sobolevVariance k α n) : ℂ) * g n - f n‖ ^ 2) := by
    have hs : Summable (fun n => ‖(weightedGaussianVector k α g - f) n‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.hasSum_norm (p := 2) (by norm_num) (weightedGaussianVector k α g - f)).summable
    have hn := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
      (weightedGaussianVector k α g - f)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
    rw [hn, ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs]
    congr 1
    funext n
    simp only [lp.coeFn_sub, Pi.sub_apply, hg n, weightedGaussianCoefficient]
    rfl
  rw [← hnorm] at herror
  have hsq := (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hr)).mp herror
  nlinarith [norm_nonneg (weightedGaussianVector k α g - f)]

/-- The Fourier Gaussian law has full support in its Sobolev Hilbert model. -/
theorem weightedGaussianLaw_isOpenPosMeasure (k α : ℝ) (hα : k + 6 < α) :
    (weightedGaussianLaw k α).IsOpenPosMeasure := by
  constructor
  intro U hU hne
  obtain ⟨f, hf⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU f hf
  exact (lt_of_lt_of_le (weightedGaussianLaw_ball_pos k α hα f hr)
    (measure_mono hball)).ne'

end DefocusingNLS

end OAI
