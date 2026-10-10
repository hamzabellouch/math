import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSlowPolynomial

namespace OAI

/-! The second free channel has the conjugate angular H expansion. -/

open Polynomial
namespace DefocusingNLS

theorem spectralPolynomialResidual_free_top (h ν η : ℂ) (P : ℂ[X]) (j : ℕ)
    (hP : P.natDegree ≤ j) :
    (spectralPolynomialResidual h ν η 0 0 P 0).coeff j=
      ((ν-2*j)*(ν+10-2*j)-η)*P.coeff j := by
  have hz : P.coeff (j+1)=0 :=
    coeff_eq_zero_of_natDegree_lt (hP.trans_lt (Nat.lt_succ_self j))
  simp only [spectralPolynomialResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative,hz,zero_mul,mul_zero,sub_zero]
  ring

theorem spectralFreeSlowCoefficient_star_succ (ell : ℕ) (q : ℂ) (k : ℕ) :
    star (spectralFreeSlowCoefficient ell (star q) 1 (k+1))=
      (((ell : ℂ)-2*q-2*k)*((ell : ℂ)-2*q+10-2*k)-((ell*(ell+10) : ℕ) : ℂ))*
        star (spectralFreeSlowCoefficient ell (star q) 1 k)/(-Complex.I*(k+1 : ℕ)) := by
  have hh := congrArg star (spectralFreeSlowCoefficient_succ ell (star q) 1 k)
  simp only [star_mul,star_sub,star_add,star_div₀,star_natCast,star_ofNat,
    Complex.star_def,Complex.conj_I,Complex.conj_conj] at hh
  simp only [Complex.star_def]
  rw [hh]
  ring

theorem spectralOutgoingPolynomial_free_second (ell : ℕ) (q νp : ℂ) (j : ℕ) :
    spectralOutgoingPolynomial νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
      1 0 (0,1) j=
        (0,(spectralFreeSlowPolynomial ell (star q) 1 j).map (starRingEnd ℂ)) := by
  induction j with
  | zero => simp [spectralOutgoingPolynomial,spectralFreeSlowPolynomial_zero]
  | succ j ih =>
    rw [spectralOutgoingPolynomial,ih]
    have hp : spectralDiagonalPolynomial 1 0=0 := by simp [spectralDiagonalPolynomial]
    have hc : spectralCrossPolynomial 1 0=0 := by simp [spectralCrossPolynomial]
    have hd : ((spectralFreeSlowPolynomial ell (star q) 1 j).map (starRingEnd ℂ)).natDegree ≤ j :=
      (natDegree_map_le).trans (spectralFreeSlowPolynomial_degree _ _ _ _)
    simp only [spectralPolynomialResidualPair,hp,hc,map_zero]
    rw [spectralPolynomialResidual_free_top _ _ _ _ _ hd]
    rw [coeff_map,spectralFreeSlowPolynomial_coefficient _ _ _ _ _ le_rfl]
    change (_, _+monomial _ (_*star _/(-Complex.I*_)))=(_, _)
    rw [← spectralFreeSlowCoefficient_star_succ,spectralFreeSlowPolynomial_succ,
      Polynomial.map_add,Polynomial.map_monomial]
    simp [spectralPolynomialResidual,radialPolynomialEuler]

end DefocusingNLS

end OAI
