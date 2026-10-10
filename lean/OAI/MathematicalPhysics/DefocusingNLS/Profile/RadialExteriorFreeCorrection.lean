import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCorrection

namespace OAI

/-! The free limiting correction satisfies the actual linear slow equation. -/

open Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExteriorLinearResidual_equation (ν : ℂ) (P : ℂ[X]) (t : ℝ) :
    radialExteriorPolynomialFunction (radialPolynomialEuler (radialPolynomialEuler P)) t+
      (2*ν+10)*radialExteriorPolynomialFunction (radialPolynomialEuler P) t+
      ν*(ν+10)*radialExteriorPolynomialFunction P t+
      Complex.I*(Real.exp (2*t)/2 : ℝ)*radialExteriorPolynomialFunction (radialPolynomialEuler P) t =
      radialExteriorPolynomialFunction (radialExteriorLinearResidual ν P) t := by
  have h := radialExteriorPolynomialResidual_equation ν 0 P t
  have hp : radialExteriorPolynomialResidual ν 0 P=radialExteriorLinearResidual ν P-P := by
    simp only [radialExteriorPolynomialResidual_eq,radialPolynomialPower,Nat.reduceAdd,pow_zero,pow_one,mul_one]
  rw [hp] at h
  have he : radialExteriorPolynomialFunction (radialExteriorLinearResidual ν P-P) t =
      radialExteriorPolynomialFunction (radialExteriorLinearResidual ν P) t-
        radialExteriorPolynomialFunction P t := by
    simp only [radialExteriorPolynomialFunction,eval_sub]
  rw [he] at h
  simp only [oddPowerNonlinearity,pow_zero,mul_one] at h
  linear_combination h

theorem radialExterior_linear_corrected_jet (ν : ℂ) (P : ℂ[X])
    (Y : ℝ → ℂ × ℂ) (t : ℝ)
    (hY : HasDerivAt Y
      ((Y t).2,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Y t).2-(2*ν+10)*(Y t).2-
        ν*(ν+10)*(Y t).1-radialExteriorPolynomialFunction (radialExteriorLinearResidual ν P) t) t) :
    HasDerivAt (fun s => radialExteriorPolynomialFunction P s+(Y s).1)
      (radialExteriorPolynomialFunction (radialPolynomialEuler P) t+(Y t).2) t ∧
    HasDerivAt (fun s => radialExteriorPolynomialFunction (radialPolynomialEuler P) s+(Y s).2)
      (-(2*ν+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*
          (radialExteriorPolynomialFunction (radialPolynomialEuler P) t+(Y t).2)-
        ν*(ν+10)*(radialExteriorPolynomialFunction P t+(Y t).1)) t := by
  have hY1 : HasDerivAt (fun s => (Y s).1) (Y t).2 t :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hY
  have hY2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hY
  refine ⟨(radialExteriorPolynomialFunction_hasDerivAt P t).add hY1,?_⟩
  apply ((radialExteriorPolynomialFunction_hasDerivAt (radialPolynomialEuler P) t).add hY2).congr_deriv
  change radialExteriorPolynomialFunction (radialPolynomialEuler (radialPolynomialEuler P)) t+
    (-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Y t).2-(2*ν+10)*(Y t).2-
      ν*(ν+10)*(Y t).1-radialExteriorPolynomialFunction (radialExteriorLinearResidual ν P) t) = _
  linear_combination radialExteriorLinearResidual_equation ν P t

theorem radialExterior_free_tail_from_correction (ν : ℂ) (T : ℝ) (j : ℕ)
    (P R : ℂ[X]) (hR : radialExteriorLinearResidual ν P=X^j*R)
    (v : ℝ →ᵇ ℂ × ℂ) (t : ℝ) (ht : T ≤ t)
    (hv : HasDerivAt (fun s => v s)
      ((2*(j : ℝ)) • v t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v t).2)+
        radialExteriorErrorMatrix ν (v t)+boundedRadialResidualAfter T R t) t) :
    let Y := radialExteriorUnweight (2*(j : ℝ)) v
    HasDerivAt (fun s => radialExteriorPolynomialFunction P s+(Y s).1)
      (radialExteriorPolynomialFunction (radialPolynomialEuler P) t+(Y t).2) t ∧
    HasDerivAt (fun s => radialExteriorPolynomialFunction (radialPolynomialEuler P) s+(Y s).2)
      (-(2*ν+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*
          (radialExteriorPolynomialFunction (radialPolynomialEuler P) t+(Y t).2)-
        ν*(ν+10)*(radialExteriorPolynomialFunction P t+(Y t).1)) t := by
  intro Y
  have hv' : HasDerivAt (fun s => v s)
      ((2*(j : ℝ)) • v t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v t).2)+
        radialExteriorErrorMatrix ν (v t)+
        (0,radialExteriorWeightedIncrement (2*(j : ℝ)) (fun _ => 0) (fun _ => 0) t (v t).1)+
        boundedRadialResidualAfter T R t) t := by
    simpa only [radialExteriorWeightedIncrement,sub_self,mul_zero,Prod.mk_zero_zero,add_zero] using hv
  have hyt := radialExteriorUnweight_hasDerivAt (2*(j : ℝ)) t ν
    (fun _ => 0) (fun _ => 0) (boundedRadialResidualAfter T R) v hv'
  change HasDerivAt Y _ t at hyt
  simp only [sub_self,Prod.mk_zero_zero,add_zero] at hyt
  rw [boundedRadialResidualAfter_factor T _ R j hR t ht] at hyt
  apply radialExterior_linear_corrected_jet ν P Y t
  apply hyt.congr_deriv
  apply Prod.ext <;> simp [radialExteriorErrorMatrix] <;> ring

end DefocusingNLS

end OAI
