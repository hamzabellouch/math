import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialEquation

namespace OAI

/-! Finite-radius coefficients obtained from the actual continuous radial profile. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def spectralClampedProfile (R : ℝ) (hR : 0 ≤ R)
    (Q : ℝ → ℂ) (hQ : Continuous Q) : ℝ →ᵇ ℂ := by
  classical
  have hb := (isCompact_Icc : IsCompact (Icc (0 : ℝ) R)).exists_bound_of_continuousOn hQ.continuousOn
  exact BoundedContinuousFunction.ofNormedAddCommGroup (fun r => Q (radialClamp R r))
    (hQ.comp (continuous_radialClamp R)) (Classical.choose hb)
    (fun r => Classical.choose_spec hb _ (radialClamp_mem R r hR))

theorem spectralClampedProfile_eq (R : ℝ) (hR : 0 ≤ R) (Q : ℝ → ℂ)
    (hQ : Continuous Q) (r : ℝ) (hr : r ∈ Icc 0 R) :
    spectralClampedProfile R hR Q hQ r=Q r := by
  change Q (radialClamp R r)=Q r
  rw [radialClamp_eq R r hr]

noncomputable def spectralRegularDiagonal (m : ℕ) (q : ℝ →ᵇ ℂ) : ℝ →ᵇ ℂ :=
  ((m+1 : ℕ) : ℂ) • (q^m*(star q)^m)

noncomputable def spectralRegularCross (m : ℕ) (q : ℝ →ᵇ ℂ) : ℝ →ᵇ ℂ :=
  (m : ℂ) • (q^(m+1)*(star q)^(m-1))

theorem spectralRegularDiagonal_apply (m : ℕ) (q : ℝ →ᵇ ℂ) (r : ℝ) :
    spectralRegularDiagonal m q r=spectralDiagonalCoefficient m (q r) := by
  simp only [spectralRegularDiagonal,spectralDiagonalCoefficient,
    BoundedContinuousFunction.smul_apply,BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.pow_apply,BoundedContinuousFunction.star_apply,smul_eq_mul]
  ring

theorem spectralRegularCross_apply (m : ℕ) (q : ℝ →ᵇ ℂ) (r : ℝ) :
    spectralRegularCross m q r=spectralCrossCoefficient m (q r) := by
  simp only [spectralRegularCross,spectralCrossCoefficient,
    BoundedContinuousFunction.smul_apply,BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.pow_apply,BoundedContinuousFunction.star_apply,smul_eq_mul]
  ring

end DefocusingNLS

end OAI
