import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorVelocity
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

/-! The complex logarithmic coefficients equal the real mass and transport coefficients. -/

namespace DefocusingNLS

theorem spectralLogGauge_mass (q dq : ℂ) :
    dq/q+star dq/star q=((2*(star q*dq).re/Complex.normSq q : ℝ) : ℂ) := by
  have hs : star (dq/q)=star dq/star q := by simp only [star_div₀]
  rw [show 2*(star q*dq).re/Complex.normSq q=2*((star q*dq).re/Complex.normSq q) by ring,
    ← hs,← complex_logDerivative_re]
  generalize dq/q=v
  apply Complex.ext <;> simp
  ring

theorem spectralLogGauge_transport (q dq : ℂ) (r : ℝ) :
    (r : ℂ)/2-Complex.I*(dq/q-star dq/star q)=
      ((r/2+2*(star q*dq).im/Complex.normSq q : ℝ) : ℂ) := by
  have hs : star (dq/q)=star dq/star q := by simp only [star_div₀]
  rw [show 2*(star q*dq).im/Complex.normSq q=2*((star q*dq).im/Complex.normSq q) by ring,
    ← hs,← complex_logDerivative_im]
  generalize dq/q=v
  apply Complex.ext <;> simp
  ring

end DefocusingNLS

end OAI
