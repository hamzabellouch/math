import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansion
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace OAI

/-! The finite exterior expansion has the precise differential residual required by the tail equation. -/

open Polynomial
namespace DefocusingNLS

noncomputable def radialExteriorPolynomialFunction (P : ℂ[X]) (t : ℝ) : ℂ :=
  P.eval (Real.exp (-2*t) : ℂ)

theorem radialExteriorPolynomialFunction_hasDerivAt (P : ℂ[X]) (t : ℝ) :
    HasDerivAt (radialExteriorPolynomialFunction P)
      (radialExteriorPolynomialFunction (radialPolynomialEuler P) t) t := by
  have hx : HasDerivAt (fun s : ℝ => Real.exp (-2*s)) (-2*Real.exp (-2*t)) t := by
    convert ((hasDerivAt_id t).const_mul (-2)).exp using 1 <;> simp [mul_comm]
  have hp : HasDerivAt (fun x : ℝ => P.eval (x : ℂ))
      (P.derivative.eval (Real.exp (-2*t) : ℂ)) (Real.exp (-2*t)) := by
    simpa only using! (P.hasDerivAt (Real.exp (-2*t) : ℂ)).comp_ofReal
  have h := hp.scomp t hx
  convert! h using 1
  simp only [radialExteriorPolynomialFunction,radialPolynomialEuler,eval_mul,eval_C,eval_X,
    Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  ring

theorem radialPolynomialPower_eval (n : ℕ) (P : ℂ[X]) (x : ℝ) :
    (radialPolynomialPower n P).eval (x : ℂ)=oddPowerNonlinearity n (P.eval (x : ℂ)) := by
  have hc : (Polynomial.mapRingHom (starRingEnd ℂ) P).eval (x : ℂ) =
      star (P.eval (x : ℂ)) := by
    simpa only [Polynomial.coe_mapRingHom,Complex.star_def,Complex.conj_ofReal] using
      (Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) (x : ℂ))
  simp only [radialPolynomialPower,eval_mul,eval_pow,hc,oddPowerNonlinearity]

theorem radialExteriorPolynomialResidual_equation (ν : ℂ) (n : ℕ) (P : ℂ[X]) (t : ℝ) :
    radialExteriorPolynomialFunction (radialPolynomialEuler (radialPolynomialEuler P)) t+
      (2*ν+10)*radialExteriorPolynomialFunction (radialPolynomialEuler P) t+
      ν*(ν+10)*radialExteriorPolynomialFunction P t+
      Complex.I*(Real.exp (2*t)/2 : ℝ)*radialExteriorPolynomialFunction (radialPolynomialEuler P) t-
      oddPowerNonlinearity n (radialExteriorPolynomialFunction P t) =
      radialExteriorPolynomialFunction (radialExteriorPolynomialResidual ν n P) t := by
  have he : Real.exp (2*t)*Real.exp (-2*t)=1 := by
    rw [← Real.exp_add]
    simp
  have hei : (Real.exp (2*t) : ℂ)*(Real.exp (-2*t) : ℂ)=1 := by exact_mod_cast he
  simp only [radialExteriorPolynomialFunction,radialExteriorPolynomialResidual,eval_add,eval_sub,
    eval_mul,eval_C,radialPolynomialPower_eval]
  simp only [radialPolynomialEuler,eval_mul,eval_C,eval_X]
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
  linear_combination -Complex.I*P.derivative.eval (Real.exp (-2*t) : ℂ)*hei

theorem radialExteriorPolynomialResidual_factor (ν : ℂ) (n : ℕ) (m : ℂ) (j : ℕ) :
    ∃ R : ℂ[X], ∀ t : ℝ,
      radialExteriorPolynomialFunction
        (radialExteriorPolynomialResidual ν n (radialExteriorExpansion ν n m j)) t =
        (Real.exp (-(2*(j : ℝ))*t) : ℂ)*radialExteriorPolynomialFunction R t := by
  obtain ⟨R,hR⟩ := radialExteriorExpansion_residual ν n m j
  refine ⟨R,?_⟩
  intro t
  simp only [radialExteriorPolynomialFunction,hR,eval_mul,eval_pow,eval_X]
  congr 1
  rw [← Complex.ofReal_pow,← Real.exp_nat_mul]
  congr 2
  ring

end DefocusingNLS

end OAI
