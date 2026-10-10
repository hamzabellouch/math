import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityEquation

namespace OAI

/-! The real and imaginary balances in the stationary amplitude-phase equation. -/

namespace DefocusingNLS

theorem radialPolar_real_balance (A A₁ A₂ w r b P : ℝ)
    (hA : -A₂-11/r*A₁+P*A=(b+r^2/16-w^2/4)*A) :
    A₂+11/r*A₁-A*((w-r/2)/2)^2-r/2*A*((w-r/2)/2)+b*A=P*A := by
  nlinarith

theorem radialPolar_imag_balance (A A₁ w w₁ r a : ℝ) (hA : A ≠ 0) (hr : r ≠ 0)
    (hw : w₁=6-2*a-11/r*w-2*w*A₁/A) :
    2*A₁*((w-r/2)/2)+A*((w₁-1/2)/2)+11/r*A*((w-r/2)/2)+r/2*A₁+a*A=0 := by
  rw [hw]
  field_simp [hA,hr]
  ring

end DefocusingNLS

end OAI
