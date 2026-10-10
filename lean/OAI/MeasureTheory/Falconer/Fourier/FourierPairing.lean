import OAI.MeasureTheory.Falconer.Fourier.GaussianRepresentation
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ProbabilityTheory ComplexConjugate
open scoped ENNReal NNReal RealInnerProductSpace

theorem integral_charFun_swap (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ t, charFun μ t ∂ν) = ∫ x, charFun ν x ∂μ := by
  simp only [charFun_apply]
  rw [integral_integral_swap]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [real_inner_comm]))
  · exact (integrable_const (1 : ℝ)).mono (by fun_prop) (by filter_upwards with z; simp [Function.uncurry,Complex.norm_exp])

noncomputable def reflectedMeasure (μ : Measure Plane) : Measure Plane := μ.map (fun x => -x)

instance reflectedMeasure_finite (μ : Measure Plane) [IsFiniteMeasure μ] :
    IsFiniteMeasure (reflectedMeasure μ) := by unfold reflectedMeasure; infer_instance

theorem charFun_reflected (μ : Measure Plane) (t : Plane) :
    charFun (reflectedMeasure μ) t = conj (charFun μ t) := by
  have h := charFun_map_smul (μ := μ) (-1 : ℝ) t
  simpa only [neg_one_smul,charFun_neg,reflectedMeasure] using h

theorem charFun_self_convolution_reflected (μ : Measure Plane) [IsFiniteMeasure μ] (t : Plane) :
    charFun (μ ∗ reflectedMeasure μ) t = (‖charFun μ t‖^2 : ℂ) := by
  rw [charFun_conv,charFun_reflected,Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

theorem gaussian_charFun_square_integral (μ : Measure Plane) [IsFiniteMeasure μ] :
    (∫ t : Plane, ‖charFun μ t‖^2 ∂stdGaussian Plane) =
      ∫ x : Plane, ∫ y : Plane, Real.exp (-‖x-y‖^2/2) ∂μ ∂μ := by
  have hs := integral_charFun_swap (μ ∗ reflectedMeasure μ) (stdGaussian Plane)
  simp only [charFun_self_convolution_reflected,charFun_stdGaussian] at hs
  have hc : (∫ z : Plane, Complex.exp (- (‖z‖ : ℂ)^2/2) ∂(μ ∗ reflectedMeasure μ)) =
      ∫ x : Plane, ∫ y : Plane, Complex.exp (- (‖x-y‖ : ℂ)^2/2) ∂μ ∂μ := by
    rw [integral_conv]
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [reflectedMeasure,integral_map (by fun_prop) (by fun_prop)]
        simp only [sub_eq_add_neg])
    · apply (integrable_const (1 : ℝ)).mono (by fun_prop)
      filter_upwards with z
      rw [Complex.norm_exp]
      simp only [norm_one,Complex.div_ofNat_re,Complex.neg_re,← Complex.ofReal_pow,
        Complex.ofReal_re]
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg ‖z‖]

  have hs' : (∫ t : Plane, (‖charFun μ t‖^2 : ℂ) ∂stdGaussian Plane) =
      ∫ x : Plane, ∫ y : Plane, Complex.exp (- (‖x-y‖ : ℂ)^2/2) ∂μ ∂μ := hs.trans hc
  have he (r : ℝ) : Complex.exp (- (r : ℂ)^2/2) = (Real.exp (-r^2/2) : ℂ) := by
    simp only [Complex.ofReal_exp,Complex.ofReal_div,Complex.ofReal_neg,
      Complex.ofReal_pow,Complex.ofReal_ofNat]

  simp_rw [he,← Complex.ofReal_pow,integral_complex_ofReal] at hs'
  exact Complex.ofReal_injective hs'

end PlanarFalconer

end OAI
