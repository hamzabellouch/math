import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansion

namespace OAI

/-! Triangular polynomial residuals for the two circular spectral channels. -/

open Polynomial
namespace DefocusingNLS

noncomputable def spectralPolynomialResidual (h ν η : ℂ) (A B U V : ℂ[X]) : ℂ[X] :=
  radialPolynomialEuler (radialPolynomialEuler U)+C (2*ν+10)*radialPolynomialEuler U+
    C (ν*(ν+10)-η)*U-C (h*Complex.I)*U.derivative-A*U-B*V

theorem spectralPolynomialResidual_low_difference (h ν η : ℂ) (A B U V U' V' : ℂ[X])
    (k : ℕ) (hU : X^(k+1) ∣ U'-U) (hV : X^(k+1) ∣ V'-V) :
    (spectralPolynomialResidual h ν η A B U' V').coeff k-
      (spectralPolynomialResidual h ν η A B U V).coeff k=
        -h*Complex.I*((U'-U).coeff (k+1)*(k+1 : ℕ)) := by
  have he : U'.coeff k=U.coeff k := by
    have he := (X_pow_dvd_iff.mp hU) k (Nat.lt_succ_self k)
    rw [coeff_sub] at he
    exact sub_eq_zero.mp he
  have hAU : (A*U').coeff k=(A*U).coeff k := by
    have hd : X^(k+1) ∣ A*U'-A*U := by
      rw [← mul_sub]
      exact dvd_mul_of_dvd_right hU A
    have he := (X_pow_dvd_iff.mp hd) k (Nat.lt_succ_self k)
    rw [coeff_sub] at he
    exact sub_eq_zero.mp he
  have hBV : (B*V').coeff k=(B*V).coeff k := by
    have hd : X^(k+1) ∣ B*V'-B*V := by
      rw [← mul_sub]
      exact dvd_mul_of_dvd_right hV B
    have he := (X_pow_dvd_iff.mp hd) k (Nat.lt_succ_self k)
    rw [coeff_sub] at he
    exact sub_eq_zero.mp he
  simp only [spectralPolynomialResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative,he,hAU,hBV]
  push_cast
  ring

theorem spectralPolynomialResidual_update (h ν η : ℂ) (A B U V : ℂ[X])
    (j k : ℕ) (c d : ℂ) (hk : k ≤ j) :
    (spectralPolynomialResidual h ν η A B (U+monomial (j+1) c) (V+monomial (j+1) d)).coeff k=
      (spectralPolynomialResidual h ν η A B U V).coeff k-
        if k=j then h*Complex.I*((j+1 : ℕ)*c) else 0 := by
  have hU : X^(k+1) ∣ U+monomial (j+1) c-U := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    have hne : j+1 ≠ i := by omega
    simp [coeff_monomial,hne]
  have hV : X^(k+1) ∣ V+monomial (j+1) d-V := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    have hne : j+1 ≠ i := by omega
    simp [coeff_monomial,hne]
  have he := spectralPolynomialResidual_low_difference h ν η A B U V
    (U+monomial (j+1) c) (V+monomial (j+1) d) k hU hV
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
