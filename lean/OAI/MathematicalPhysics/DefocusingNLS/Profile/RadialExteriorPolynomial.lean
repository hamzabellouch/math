import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorNonlinearTail
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum

namespace OAI

/-! Polynomial residuals for the exterior expansion in x = r⁻². -/

open Polynomial
namespace DefocusingNLS

noncomputable def radialPolynomialEuler (P : ℂ[X]) : ℂ[X] :=
  C (-2)* (X*P.derivative)

theorem radialPolynomialEuler_coeff (P : ℂ[X]) (k : ℕ) :
    (radialPolynomialEuler P).coeff k=(-2*(k : ℂ))*P.coeff k := by
  cases k with
  | zero => simp [radialPolynomialEuler]
  | succ k =>
    simp only [radialPolynomialEuler,coeff_C_mul,coeff_X_mul,coeff_derivative]
    push_cast
    ring

noncomputable def radialPolynomialPower (n : ℕ) (P : ℂ[X]) : ℂ[X] :=
  P^(n+1)*(Polynomial.mapRingHom (starRingEnd ℂ) P)^n

theorem radialPolynomialPower_difference_dvd (n k : ℕ) (P Q : ℂ[X])
    (h : X^k ∣ Q-P) : X^k ∣ radialPolynomialPower n Q-radialPolynomialPower n P := by
  have hs : X^k ∣ Polynomial.mapRingHom (starRingEnd ℂ) Q-
      Polynomial.mapRingHom (starRingEnd ℂ) P := by
    have hs := map_dvd (Polynomial.mapRingHom (starRingEnd ℂ)) h
    simpa only [map_sub,map_pow,Polynomial.coe_mapRingHom,Polynomial.map_X] using hs
  have hp := h.trans (sub_dvd_pow_sub_pow Q P (n+1))
  have hsp := hs.trans (sub_dvd_pow_sub_pow
    (Polynomial.mapRingHom (starRingEnd ℂ) Q) (Polynomial.mapRingHom (starRingEnd ℂ) P) n)
  unfold radialPolynomialPower
  rw [show Q^(n+1)*(Polynomial.mapRingHom (starRingEnd ℂ) Q)^n-
      P^(n+1)*(Polynomial.mapRingHom (starRingEnd ℂ) P)^n =
      (Q^(n+1)-P^(n+1))*(Polynomial.mapRingHom (starRingEnd ℂ) Q)^n+
      P^(n+1)*((Polynomial.mapRingHom (starRingEnd ℂ) Q)^n-
        (Polynomial.mapRingHom (starRingEnd ℂ) P)^n) by ring]
  exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hsp _)

noncomputable def radialExteriorPolynomialResidual (ν : ℂ) (n : ℕ) (P : ℂ[X]) : ℂ[X] :=
  radialPolynomialEuler (radialPolynomialEuler P)+C (2*ν+10)*radialPolynomialEuler P+
    C (ν*(ν+10))*P-C Complex.I*P.derivative-radialPolynomialPower n P

theorem radialExteriorPolynomialResidual_low_difference (ν : ℂ) (n k : ℕ) (P Q : ℂ[X])
    (h : X^(k+1) ∣ Q-P) :
    (radialExteriorPolynomialResidual ν n Q).coeff k-
      (radialExteriorPolynomialResidual ν n P).coeff k =
      -Complex.I*((Q-P).coeff (k+1)*(k+1 : ℕ)) := by
  have he : Q.coeff k=P.coeff k := by
    have he := (X_pow_dvd_iff.mp h) k (Nat.lt_succ_self k)
    rw [coeff_sub] at he
    exact sub_eq_zero.mp he
  have hn : (radialPolynomialPower n Q).coeff k=(radialPolynomialPower n P).coeff k := by
    have hn := X_pow_dvd_iff.mp (radialPolynomialPower_difference_dvd n (k+1) P Q h)
      k (Nat.lt_succ_self k)
    rw [coeff_sub] at hn
    exact sub_eq_zero.mp hn
  simp only [radialExteriorPolynomialResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative,he,hn]
  push_cast
  ring

theorem radialExteriorPolynomialResidual_update (ν : ℂ) (n j k : ℕ) (P : ℂ[X]) (c : ℂ)
    (hk : k ≤ j) :
    (radialExteriorPolynomialResidual ν n (P+monomial (j+1) c)).coeff k =
      (radialExteriorPolynomialResidual ν n P).coeff k-
        if k=j then Complex.I*((j+1 : ℕ)*c) else 0 := by
  have hd : X^(k+1) ∣ P+monomial (j+1) c-P := by
    apply X_pow_dvd_iff.mpr
    intro d hdk
    have hne : j+1 ≠ d := by omega
    simp [coeff_monomial,hne]
  have he := radialExteriorPolynomialResidual_low_difference ν n k P
    (P+monomial (j+1) c) hd
  by_cases hkj : k=j
  · subst k
    simp only [coeff_monomial,ite_true,add_sub_cancel_left] at he ⊢
    linear_combination he
  · have hne : j+1 ≠ k+1 := by omega
    simp only [coeff_monomial,hne,ite_false,add_sub_cancel_left,zero_mul,mul_zero] at he
    simp only [hkj,ite_false,sub_zero]
    exact sub_eq_zero.mp he

end DefocusingNLS

end OAI
