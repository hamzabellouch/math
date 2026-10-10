import OAI.MeasureTheory.Falconer.Slicing.GaussianLocalization
import OAI.MeasureTheory.Falconer.Measures.WeightedIntegralSquare
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # Gaussian convolution of a finite measure Fourier transform -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace
variable {d : ℕ}

noncomputable def euclideanFourierPhase (v x : Space d) : ℂ :=
  Complex.exp (((-(2*Real.pi)*inner ℝ x v:ℝ):ℂ)*Complex.I)

theorem sourceFourier_phase (μ : Measure (Space d)) (v : Space d) :
    PlanarFalconer.sourceFourier μ v = ∫ x, euclideanFourierPhase v x ∂μ := by
  simp only [PlanarFalconer.sourceFourier,charFun_apply,inner_smul_right,euclideanFourierPhase]

theorem shifted_gaussian_fourier (v x : Space d) :
    𝓕 (fun u : Space d => (Real.exp (-2*‖u-v‖^2):ℂ)) x =
      euclideanFourierPhase v x*
        (((Real.pi/2)^((d:ℝ)/2)*Real.exp (-(Real.pi^2/2)*‖x‖^2):ℝ):ℂ) := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure (Space d)) (innerₗ (Space d))
    (fun u : Space d => (Real.exp (-2*‖u‖^2):ℂ)) (-v)) x
  change 𝓕 (fun u : Space d => (Real.exp (-2*‖u+(-v)‖^2):ℂ)) x =
    Real.fourierChar (inner ℝ (-v) x) •
      𝓕 (fun u : Space d => (Real.exp (-2*‖u‖^2):ℂ)) x at h
  rw [PlanarFalconer.source_gaussian_fourier (by norm_num : (0:ℝ) < 2)] at h
  have hp : (Real.fourierChar (inner ℝ (-v) x) : ℂ) = euclideanFourierPhase v x := by
    rw [Real.fourierChar_apply,euclideanFourierPhase,inner_neg_left,real_inner_comm x v]
    congr 1
    push_cast
    ring
  have hd : Module.finrank ℝ (Space d) = d := by simp [Space]
  simpa only [hd,sub_eq_add_neg,Circle.smul_def,smul_eq_mul,hp] using h

theorem gaussian_convolution_identity (β : Measure (Space d)) [IsFiniteMeasure β]
    (v : Space d) :
    (∫ u : Space d, (Real.exp (-2*‖u-v‖^2):ℂ)*PlanarFalconer.sourceFourier β u) =
      (((Real.pi/2:ℝ)^((d:ℝ)/2):ℝ):ℂ)*
        ∫ x, (Real.exp (-(Real.pi^2/2)*‖x‖^2):ℂ)*euclideanFourierPhase v x ∂β := by
  have hi : Integrable (fun u : Space d => (Real.exp (-2*‖u-v‖^2):ℂ)) :=
    ((PlanarFalconer.gaussian_lebesgue_integrable (V := Space d) (by norm_num : (0:ℝ)<2)).comp_sub_right v).ofReal
  rw [PlanarFalconer.sourceFourier_integral_swap β _ hi]
  simp only [shifted_gaussian_fourier,Complex.ofReal_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

end Falconer

end OAI
