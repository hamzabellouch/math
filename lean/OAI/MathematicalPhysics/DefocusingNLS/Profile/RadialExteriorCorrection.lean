import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedExpansion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorUnweight

namespace OAI

/-! Correcting the finite expansion gives the original nonlinear slow-profile equation. -/

namespace DefocusingNLS

open Polynomial

theorem radialExterior_corrected_jet (ν : ℂ) (n : ℕ) (P : ℂ[X])
    (Y : ℝ → ℂ × ℂ) (t : ℝ)
    (hY : HasDerivAt Y
      ((Y t).2,
        -Complex.I*(Real.exp (2*t)/2 : ℝ)*(Y t).2-(2*ν+10)*(Y t).2-
          ν*(ν+10)*(Y t).1+
          oddPowerNonlinearity n (radialExteriorPolynomialFunction P t+(Y t).1)-
          oddPowerNonlinearity n (radialExteriorPolynomialFunction P t)-
          radialExteriorPolynomialFunction (radialExteriorPolynomialResidual ν n P) t) t) :
    HasDerivAt (fun s => radialExteriorPolynomialFunction P s+(Y s).1)
      (radialExteriorPolynomialFunction (radialPolynomialEuler P) t+(Y t).2) t ∧
    HasDerivAt (fun s => radialExteriorPolynomialFunction (radialPolynomialEuler P) s+(Y s).2)
      (-(2*ν+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*
          (radialExteriorPolynomialFunction (radialPolynomialEuler P) t+(Y t).2)-
        ν*(ν+10)*(radialExteriorPolynomialFunction P t+(Y t).1)+
        oddPowerNonlinearity n (radialExteriorPolynomialFunction P t+(Y t).1)) t := by
  have hY1 : HasDerivAt (fun s => (Y s).1) (Y t).2 t :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hY
  have hY2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hY
  refine ⟨(radialExteriorPolynomialFunction_hasDerivAt P t).add hY1,?_⟩
  apply ((radialExteriorPolynomialFunction_hasDerivAt (radialPolynomialEuler P) t).add hY2).congr_deriv
  change radialExteriorPolynomialFunction (radialPolynomialEuler (radialPolynomialEuler P)) t+
    (-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Y t).2-(2*ν+10)*(Y t).2-
      ν*(ν+10)*(Y t).1+
      oddPowerNonlinearity n (radialExteriorPolynomialFunction P t+(Y t).1)-
      oddPowerNonlinearity n (radialExteriorPolynomialFunction P t)-
      radialExteriorPolynomialFunction (radialExteriorPolynomialResidual ν n P) t) = _
  linear_combination radialExteriorPolynomialResidual_equation ν n P t

end DefocusingNLS

end OAI
