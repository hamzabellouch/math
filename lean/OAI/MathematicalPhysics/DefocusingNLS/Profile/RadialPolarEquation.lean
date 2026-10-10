import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolarDerivative

namespace OAI

/-! Scalar real and imaginary balances imply the stationary complex radial equation. -/

namespace DefocusingNLS

theorem radialPolar_stationary_of_balances (A φ : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hφ : Differentiable ℝ φ) (r a b P : ℝ)
    (hDA : DifferentiableAt ℝ (deriv A) r) (hDφ : DifferentiableAt ℝ (deriv φ) r)
    (hRe : deriv (deriv A) r+11/r*deriv A r-A r*(deriv φ r)^2-
      r/2*A r*deriv φ r+b*A r=P*A r)
    (hIm : 2*deriv A r*deriv φ r+A r*deriv (deriv φ) r+
      11/r*A r*deriv φ r+r/2*deriv A r+a*A r=0) :
    deriv (deriv (radialPolar A φ)) r+(11/r : ℝ)*deriv (radialPolar A φ) r+
      Complex.I*((r/2 : ℝ)*deriv (radialPolar A φ) r+(a : ℂ)*radialPolar A φ r)+
        (b : ℂ)*radialPolar A φ r=(P : ℂ)*radialPolar A φ r := by
  rw [radialPolar_second_derivative A φ hA hφ r hDA hDφ,
    (radialPolar_hasDerivAt A φ hA hφ r).deriv]
  unfold radialPolar
  have hReC := congrArg (fun x : ℝ => (x : ℂ)) hRe
  have hImC := congrArg (fun x : ℝ => (x : ℂ)) hIm
  push_cast at hReC hImC ⊢
  linear_combination Complex.exp (Complex.I*(φ r : ℂ))*hReC+
    Complex.I*Complex.exp (Complex.I*(φ r : ℂ))*hImC+
    ((r : ℂ)/2)*(A r : ℂ)*((deriv φ r : ℝ) : ℂ)*Complex.exp (Complex.I*(φ r : ℂ))*Complex.I_sq

end DefocusingNLS

end OAI
