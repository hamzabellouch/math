import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexVirial
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularScalarEstimates
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralComplexWeightedSquare

namespace OAI

/-! The zero-pressure complex form is the nonnegative radial-plus-angular
energy appearing in the normalized spectral contradiction. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialComplexAngularForm_zero_nonneg (n : ℕ) (z : ProfileMatchingBall)
    (eta R : ℝ) (he : 0 ≤ eta) (hR : 0 ≤ R) (f : ℝ → ℂ) :
    0 ≤ radialComplexAngularForm n z eta R (fun _ => 0) f := by
  exact add_nonneg (radialAngularScalarForm_nonneg n z eta R he hR _ _ (by simp))
    (radialAngularScalarForm_nonneg n z eta R he hR _ _ (by simp))

theorem radialComplexAngularForm_zero_eq (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (eta R : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    radialComplexAngularForm n z eta R (fun _ => 0) f =
      (∫ r in (0 : ℝ)..R, radialMassDensity n z r*‖deriv f r‖^2)+
      eta*(∫ r in (0 : ℝ)..R, radialAngularDensity n z r*‖f r‖^2) := by
  have hd := spectralComplex_integral_sq R (radialMassDensity n z) (deriv f)
    (radialMassDensity_continuous n z hX hz) hf.continuous_deriv_one
  have hv := spectralComplex_integral_sq R (radialAngularDensity n z) f
    (radialAngularDensity_continuous n z hX hz) hf.continuous
  unfold radialComplexAngularForm radialAngularScalarForm
  rw [radialScalarForm_diag,radialScalarForm_diag,radialAngularForm_diag,radialAngularForm_diag,
    radialComplex_deriv_re f (hf.differentiable (by norm_num)),
    radialComplex_deriv_im f (hf.differentiable (by norm_num))]
  simp only [mul_zero,zero_mul,intervalIntegral.integral_zero,add_zero]
  linear_combination hd+eta*hv

end DefocusingNLS

end OAI
