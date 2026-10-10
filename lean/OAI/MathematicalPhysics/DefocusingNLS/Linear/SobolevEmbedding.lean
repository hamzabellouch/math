import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianRealization
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.BlowupRate
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-!
# Continuous point observation in the Fourier Sobolev model

For `k > 6`, the Fourier coefficients are absolutely summable in dimension
twelve. Their sum is therefore a bounded linear observation (evaluation at
the center of the torus), suitable for the blowup/nonextension argument.
-/

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace DefocusingNLS

lemma sobolev_observation_weight_sq (k : ℝ) (n : frequencyLattice) :
    ‖(((1 + ‖n‖ ^ 2) ^ (-k / 2) : ℝ) : ℂ)‖ ^ 2 = (1 + ‖n‖ ^ 2) ^ (-k) := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The inverse Sobolev weights form an `ℓ²` vector exactly above dimension/2. -/
noncomputable def sobolevObservationVector (k : ℝ) (hk : 6 < k) : FourierL2 :=
  ⟨fun n => (((1 + ‖n‖ ^ 2) ^ (-k / 2) : ℝ) : ℂ), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sobolev_observation_weight_sq,
      zero_sub] using summable_sobolev_variances 0 k (by linarith)⟩

/-- Evaluation at the torus center, in the Fourier model of `H^k`. -/
noncomputable def sobolevCenterEvaluation (k : ℝ) (hk : 6 < k) : FourierL2 →L[ℂ] ℂ :=
  innerSL ℂ (sobolevObservationVector k hk)

/-- The bounded observation is the sum of the actual, unweighted coefficients. -/
theorem hasSum_sobolevFourierCoefficient (k : ℝ) (hk : 6 < k) (f : FourierL2) :
    HasSum (sobolevFourierCoefficient k f) (sobolevCenterEvaluation k hk f) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (sobolevObservationVector k hk) f
  change HasSum (fun n => sobolevFourierCoefficient k f n) _
  simpa [sobolevObservationVector, sobolevCenterEvaluation, sobolevFourierCoefficient,
    RCLike.inner_apply', Algebra.smul_def, mul_comm] using h

theorem sobolevCenterEvaluation_eq_tsum (k : ℝ) (hk : 6 < k) (f : FourierL2) :
    sobolevCenterEvaluation k hk f = ∑' n, sobolevFourierCoefficient k f n :=
  (hasSum_sobolevFourierCoefficient k hk f).tsum_eq.symm

/-- Absolute summability of the unweighted Fourier series. -/
theorem summable_norm_sobolevFourierCoefficient (k : ℝ) (hk : 6 < k) (f : FourierL2) :
    Summable (fun n => ‖sobolevFourierCoefficient k f n‖) :=
  (hasSum_sobolevFourierCoefficient k hk f).summable.norm

theorem sobolevCenterEvaluation_bound (k : ℝ) (hk : 6 < k) (f : FourierL2) :
    ‖sobolevCenterEvaluation k hk f‖ ≤ ‖sobolevObservationVector k hk‖ * ‖f‖ := by
  change ‖inner ℂ (sobolevObservationVector k hk) f‖ ≤ _
  exact norm_inner_le_norm _ _

/-- A positive self-similar center amplitude obstructs continuous continuation
in the concrete Fourier Sobolev space. -/
theorem no_sobolev_extension_of_positive_center_rate
    (k : ℝ) (hk : 6 < k) (u : ℝ → FourierL2) (T a c : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hblowup : Filter.Tendsto
      (fun t => (T - t) ^ a * ‖sobolevCenterEvaluation k hk (u t)‖)
      (nhdsWithin T (Set.Iio T)) (nhds c)) :
    ¬ ContinuousWithinAt u (Set.Iio T) T :=
  no_continuous_extension_of_positive_rescaled_norm u (sobolevCenterEvaluation k hk)
    T a c ha hc (sobolevCenterEvaluation k hk).continuous hblowup

end DefocusingNLS

end OAI
