import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GaussianMollification
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalFactorization

namespace OAI

/-! Discharge of the published transverse-oscillator input. The normalized
Gaussian Poincare inequality and an exact compact-support integration by parts
give precisely the projection inequality used by the continuum reduction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem vertical_quotient_deriv {freq : ℝ} (hf : 0 < freq)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (z : ℝ) :
    deriv (fun x => u x/verticalMode freq x) z =
      (deriv u z+freq*z*u z)/verticalMode freq z := by
  have hn := (verticalMode_positive hf z).ne'
  rw [((hu.differentiable (by norm_num) z).hasDerivAt.fun_div
    (verticalMode_hasDerivAt freq z) hn).deriv]
  field_simp [hn]
  ring

/-- The exact harmonic-oscillator projection inequality. -/
theorem publishedVerticalOscillatorGap : PublishedVerticalOscillatorGap := by
  intro freq hf u hu hc
  let v : ℝ → ℝ := fun z => u z/verticalMode freq z
  have hv : ContDiff ℝ 1 v := hu.div ((verticalMode_smooth freq).of_le (by simp))
    (fun z => (verticalMode_positive hf z).ne')
  have hvc : HasCompactSupport v := by
    change HasCompactSupport (fun z => u z*(verticalMode freq z)⁻¹)
    exact hc.mul_right
  have hm (z : ℝ) : verticalMode freq z^2*v z^2 = u z^2 := by
    dsimp [v]
    field_simp [(verticalMode_positive hf z).ne']
  have ha (z : ℝ) : verticalMode freq z^2*v z = u z*verticalMode freq z := by
    dsimp [v]
    field_simp [(verticalMode_positive hf z).ne']
  have hd (z : ℝ) : verticalMode freq z^2*(deriv v z)^2 =
      (deriv u z+freq*z*u z)^2 := by
    rw [show deriv v z = _ from vertical_quotient_deriv hf u hu z]
    field_simp [(verticalMode_positive hf z).ne']
  have h := gaussian_scalar_poincare hf v hv hvc
  simp_rw [hm,ha,hd] at h
  have he := vertical_factorized_energy freq u hu hc
  linarith

end ContinuumCoulomb

end

end OAI
