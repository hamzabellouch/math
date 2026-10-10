import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedPairing

namespace OAI

/-! Uniform C1 control on the ball bounds the completed harmonic energy. -/

open Set MeasureTheory
open scoped SchwartzMap ENNReal
namespace DefocusingNLS

theorem spectralHarmonicNorm_le_sum (ell : ℕ) (R : ℝ)
    (u : SpectralHarmonicEnergy ell R) :
    ‖u‖ ≤ ‖spectralHarmonicValue ell R u‖+‖spectralHarmonicDerivative ell R u‖+
      ‖spectralHarmonicAngularValue ell R u‖ := by
  have he := spectralHarmonicEnergy_norm_sq ell R u
  rw [spectralRadialEnergy_norm_sq] at he
  change ‖u‖^2=‖spectralHarmonicValue ell R u‖^2+
    ‖spectralHarmonicDerivative ell R u‖^2+‖spectralHarmonicAngularValue ell R u‖^2 at he
  have hv := norm_nonneg (spectralHarmonicValue ell R u)
  have hd := norm_nonneg (spectralHarmonicDerivative ell R u)
  have ha := norm_nonneg (spectralHarmonicAngularValue ell R u)
  nlinarith [norm_nonneg u,mul_nonneg hv hd,mul_nonneg hv ha,mul_nonneg hd ha]

theorem spectralSmoothHarmonic_uniform_bound (ell : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : 𝓢(ℝ,ℂ)) (d : ℝ), 0 ≤ d →
      (∀ r ∈ Icc 0 R, ‖f r‖ ≤ d) → (∀ r ∈ Icc 0 R, ‖deriv f r‖ ≤ d) →
      ‖spectralHarmonicSmoothEmbedding ell R f‖ ≤ C*d := by
  let c : ℝ := (measureUnivNNReal (radialPressureMeasure R) : ℝ)^((2 : ℝ≥0∞).toReal)⁻¹
  let a : ℝ := (measureUnivNNReal (spectralAngularMeasure R) : ℝ)^((2 : ℝ≥0∞).toReal)⁻¹
  let k : ℝ := ‖(Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)‖
  have hc : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  have ha : 0 ≤ a := Real.rpow_nonneg (by positivity) _
  have hk : 0 ≤ k := norm_nonneg _
  refine ⟨2*c+k*a+1,by positivity,fun f d hd hf hdf => ?_⟩
  let u := spectralHarmonicSmoothEmbedding ell R f
  have hV : ‖spectralHarmonicValue ell R u‖ ≤ c*d := by
    apply Lp.norm_le_of_ae_bound hd
    filter_upwards [spectralHarmonicValue_smooth_ae ell R f,
      radialPressureMeasure_ae_positive R] with r hr hp
    rw [hr]
    exact hf r ⟨hp.1.le,hp.2⟩
  have hD : ‖spectralHarmonicDerivative ell R u‖ ≤ c*d := by
    apply Lp.norm_le_of_ae_bound hd
    filter_upwards [spectralHarmonicDerivative_smooth_ae ell R f,
      radialPressureMeasure_ae_positive R] with r hr hp
    rw [hr]
    exact hdf r ⟨hp.1.le,hp.2⟩
  have hA : ‖spectralSmoothAngularValue R f‖ ≤ a*d := by
    apply Lp.norm_le_of_ae_bound hd
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (spectralAngularMeasure R) ℂ
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ f),
      (spectralAngularMeasure_absolutelyContinuous R).ae_le (radialPressureMeasure_ae_positive R)]
      with r hr hp
    change spectralSmoothAngularValue R f r=f r at hr
    rw [hr]
    exact hf r ⟨hp.1.le,hp.2⟩
  have hG : ‖spectralHarmonicAngularValue ell R u‖ ≤ k*(a*d) := by
    rw [spectralHarmonicAngularValue_smooth,norm_smul]
    exact mul_le_mul_of_nonneg_left hA hk
  apply (spectralHarmonicNorm_le_sum ell R u).trans
  calc
    _ ≤ c*d+c*d+k*(a*d) := add_le_add (add_le_add hV hD) hG
    _ ≤ (2*c+k*a+1)*d := by nlinarith

end DefocusingNLS

end OAI
