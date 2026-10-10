import OAI.MeasureTheory.Falconer.Slicing.GaussianConvolution

namespace OAI

/-! # Damping a finite source measure and recovering its Fourier transform -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal FourierTransform
variable {d : ℕ}

noncomputable def gaussianDampedMeasure (β : Measure (Space d)) : Measure (Space d) :=
  β.withDensity (fun x => ENNReal.ofReal (Real.exp (-(Real.pi^2/2)*‖x‖^2)))

theorem gaussianDampedMeasure_le (β : Measure (Space d)) : gaussianDampedMeasure β ≤ β := by
  calc
    _ ≤ β.withDensity (fun _ => (1:ℝ≥0∞)) := by
      apply withDensity_mono
      filter_upwards with x
      have h : Real.exp (-(Real.pi^2/2)*‖x‖^2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (div_nonneg (sq_nonneg Real.pi) (by norm_num))) (sq_nonneg _))
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h
    _ = β := by rw [withDensity_const,one_smul]

instance gaussianDampedMeasure_finite (β : Measure (Space d)) [IsFiniteMeasure β] :
    IsFiniteMeasure (gaussianDampedMeasure β) :=
  isFiniteMeasure_of_le β (gaussianDampedMeasure_le β)

theorem sourceFourier_gaussianDampedMeasure (β : Measure (Space d)) (v : Space d) :
    PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v =
      ∫ x, (Real.exp (-(Real.pi^2/2)*‖x‖^2):ℂ)*euclideanFourierPhase v x ∂β := by
  rw [sourceFourier_phase,gaussianDampedMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,Complex.real_smul]

/-- Exact convolution formula, before the Cauchy--Schwarz bound. -/
theorem gaussian_convolution_damped (β : Measure (Space d)) [IsFiniteMeasure β]
    (v : Space d) :
    (∫ u : Space d, (Real.exp (-2*‖u-v‖^2):ℂ)*PlanarFalconer.sourceFourier β u) =
      (((Real.pi/2:ℝ)^((d:ℝ)/2):ℝ):ℂ)*
        PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v := by
  rw [gaussian_convolution_identity,sourceFourier_gaussianDampedMeasure]

end Falconer

end OAI
