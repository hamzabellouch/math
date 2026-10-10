import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialExpansion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansionEquation
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity

namespace OAI

/-! Exact evaluation of the circular polynomial residual and odd-power coefficients. -/

open Polynomial
namespace DefocusingNLS

noncomputable def spectralDiagonalCoefficient (m : ℕ) (q : ℂ) : ℂ :=
  ((m+1 : ℕ) : ℂ)*q^m*(star q)^m

noncomputable def spectralCrossCoefficient (m : ℕ) (q : ℂ) : ℂ :=
  (m : ℂ)*q^(m+1)*(star q)^(m-1)

theorem spectralCoefficient_decomposition (m : ℕ) (q v : ℂ) :
    oddPowerDerivative m q v=
      spectralDiagonalCoefficient m q*v+spectralCrossCoefficient m q*star v := by
  simp [oddPowerDerivative,spectralDiagonalCoefficient,spectralCrossCoefficient,smul_eq_mul]

theorem spectralDiagonalPolynomial_eval (m : ℕ) (P : ℂ[X]) (x : ℝ) :
    (spectralDiagonalPolynomial m P).eval (x : ℂ)=
      spectralDiagonalCoefficient m (P.eval (x : ℂ)) := by
  have hc : (Polynomial.mapRingHom (starRingEnd ℂ) P).eval (x : ℂ)=star (P.eval (x : ℂ)) := by
    simpa only [Polynomial.coe_mapRingHom,Complex.star_def,Complex.conj_ofReal] using
      (Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) (x : ℂ))
  simp only [spectralDiagonalPolynomial,spectralDiagonalCoefficient,eval_mul,eval_C,eval_pow,hc]

theorem spectralCrossPolynomial_eval (m : ℕ) (P : ℂ[X]) (x : ℝ) :
    (spectralCrossPolynomial m P).eval (x : ℂ)=
      spectralCrossCoefficient m (P.eval (x : ℂ)) := by
  have hc : (Polynomial.mapRingHom (starRingEnd ℂ) P).eval (x : ℂ)=star (P.eval (x : ℂ)) := by
    simpa only [Polynomial.coe_mapRingHom,Complex.star_def,Complex.conj_ofReal] using
      (Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) (x : ℂ))
  simp only [spectralCrossPolynomial,spectralCrossCoefficient,eval_mul,eval_C,eval_pow,hc]

theorem spectralPolynomialResidual_equation (h ν η : ℂ) (A B U V : ℂ[X]) (t : ℝ) :
    radialExteriorPolynomialFunction (radialPolynomialEuler (radialPolynomialEuler U)) t+
      (2*ν+10)*radialExteriorPolynomialFunction (radialPolynomialEuler U) t+
      (ν*(ν+10)-η)*radialExteriorPolynomialFunction U t+
      h*Complex.I*(Real.exp (2*t)/2 : ℝ)*radialExteriorPolynomialFunction (radialPolynomialEuler U) t-
      radialExteriorPolynomialFunction A t*radialExteriorPolynomialFunction U t-
      radialExteriorPolynomialFunction B t*radialExteriorPolynomialFunction V t=
      radialExteriorPolynomialFunction (spectralPolynomialResidual h ν η A B U V) t := by
  have he : Real.exp (2*t)*Real.exp (-2*t)=1 := by
    rw [← Real.exp_add]
    simp
  have hei : (Real.exp (2*t) : ℂ)*(Real.exp (-2*t) : ℂ)=1 := by exact_mod_cast he
  simp only [radialExteriorPolynomialFunction,spectralPolynomialResidual,eval_add,eval_sub,
    eval_mul,eval_C]
  simp only [radialPolynomialEuler,eval_mul,eval_C,eval_X]
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
  linear_combination -h*Complex.I*U.derivative.eval (Real.exp (-2*t) : ℂ)*hei

theorem spectralOutgoingPolynomial_residual_factor (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) :
    ∃ R : ℂ[X] × ℂ[X], ∀ t : ℝ,
      radialExteriorPolynomialFunction
        (spectralPolynomialResidualPair νp νm η m P
          (spectralOutgoingPolynomial νp νm η m P c j)).1 t=
        (Real.exp (-(2*(j : ℝ))*t) : ℂ)*radialExteriorPolynomialFunction R.1 t ∧
      radialExteriorPolynomialFunction
        (spectralPolynomialResidualPair νp νm η m P
          (spectralOutgoingPolynomial νp νm η m P c j)).2 t=
        (Real.exp (-(2*(j : ℝ))*t) : ℂ)*radialExteriorPolynomialFunction R.2 t := by
  obtain ⟨hp,hm⟩ := spectralOutgoingPolynomial_residual νp νm η m P c j
  obtain ⟨Rp,hRp⟩ := hp
  obtain ⟨Rm,hRm⟩ := hm
  refine ⟨(Rp,Rm),?_⟩
  intro t
  constructor
  · simp only [radialExteriorPolynomialFunction,hRp,eval_mul,eval_pow,eval_X]
    congr 1
    rw [← Complex.ofReal_pow,← Real.exp_nat_mul]
    congr 2
    ring
  · simp only [radialExteriorPolynomialFunction,hRm,eval_mul,eval_pow,eval_X]
    congr 1
    rw [← Complex.ofReal_pow,← Real.exp_nat_mul]
    congr 2
    ring

end DefocusingNLS

end OAI
