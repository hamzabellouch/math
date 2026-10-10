import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCorrection

namespace OAI

/-! Remove the exterior cutoff using a common tail neighborhood. -/

open Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExterior_tail_cutoff_removal (ν m : ℂ) (n j : ℕ) (δ T : ℝ)
    (P R : ℂ[X]) (hR : radialExteriorPolynomialResidual ν n P=X^j*R)
    (v : ℝ →ᵇ ℂ × ℂ) (t : ℝ) (ht : T ≤ t)
    (hP : ‖radialExteriorPolynomialFunction P t-m‖ ≤ δ)
    (hF : ‖radialExteriorPolynomialFunction P t+
      (radialExteriorUnweight (2*(j : ℝ)) v t).1-m‖ ≤ δ)
    (hv : HasDerivAt (fun s => v s)
      ((2*(j : ℝ)) • v t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v t).2)+
        radialExteriorErrorField (2*(j : ℝ)) ν (radialExteriorCutoffPower n m δ)
          (boundedRadialPolynomialAfter T P) (boundedRadialResidualAfter T R) t (v t)) t) :
    let Y := radialExteriorUnweight (2*(j : ℝ)) v
    HasDerivAt (fun s => radialExteriorPolynomialFunction P s+(Y s).1)
      (radialExteriorPolynomialFunction (radialPolynomialEuler P) t+(Y t).2) t ∧
    HasDerivAt (fun s => radialExteriorPolynomialFunction (radialPolynomialEuler P) s+(Y s).2)
      (-(2*ν+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*
          (radialExteriorPolynomialFunction (radialPolynomialEuler P) t+(Y t).2)-
        ν*(ν+10)*(radialExteriorPolynomialFunction P t+(Y t).1)+
        oddPowerNonlinearity n (radialExteriorPolynomialFunction P t+(Y t).1)) t := by
  intro Y
  have hvt : HasDerivAt (fun s => v s)
      ((2*(j : ℝ)) • v t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v t).2)+
        radialExteriorErrorMatrix ν (v t)+
        (0,radialExteriorWeightedIncrement (2*(j : ℝ)) (radialExteriorCutoffPower n m δ)
          (boundedRadialPolynomialAfter T P) t (v t).1)+boundedRadialResidualAfter T R t) t := by
    simpa only [radialExteriorErrorField,add_assoc] using hv
  have hyt := radialExteriorUnweight_hasDerivAt (2*(j : ℝ)) t ν
    (radialExteriorCutoffPower n m δ) (boundedRadialPolynomialAfter T P)
    (boundedRadialResidualAfter T R) v hvt
  change HasDerivAt Y _ t at hyt
  rw [boundedRadialPolynomialAfter_eq T P t ht] at hyt
  rw [radialExteriorCutoffPower_eq n m δ _ hP,
    radialExteriorCutoffPower_eq n m δ _ hF] at hyt
  rw [boundedRadialResidualAfter_factor T _ R j hR t ht] at hyt
  have hy : HasDerivAt Y
      ((Y t).2,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Y t).2-
        (2*ν+10)*(Y t).2-ν*(ν+10)*(Y t).1+
        oddPowerNonlinearity n (radialExteriorPolynomialFunction P t+(Y t).1)-
        oddPowerNonlinearity n (radialExteriorPolynomialFunction P t)-
        radialExteriorPolynomialFunction (radialExteriorPolynomialResidual ν n P) t) t := by
    apply hyt.congr_deriv
    apply Prod.ext <;> simp [radialExteriorErrorMatrix] <;> ring
  exact radialExterior_corrected_jet ν n P Y t hy

end DefocusingNLS

end OAI
