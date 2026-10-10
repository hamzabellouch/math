import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreePochhammer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialExpansion

namespace OAI

/-! The angular H coefficients are the coefficients of the free outgoing construction. -/

open Polynomial
namespace DefocusingNLS

noncomputable def spectralFreeSlowCoefficient (ell : ℕ) (q c : ℂ) (k : ℕ) : ℂ :=
  c*(4*Complex.I)^k*slowAsymptoticJet q (ell+6) k/(k.factorial : ℂ)

noncomputable def spectralFreeSlowPolynomial (ell : ℕ) (q c : ℂ) (j : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (j+1), monomial k (spectralFreeSlowCoefficient ell q c k)

theorem spectralFreeSlowCoefficient_zero (ell : ℕ) (q c : ℂ) :
    spectralFreeSlowCoefficient ell q c 0=c := by
  simp [spectralFreeSlowCoefficient,slowAsymptoticJet]

theorem spectralFreeSlowCoefficient_succ (ell : ℕ) (q c : ℂ) (k : ℕ) :
    spectralFreeSlowCoefficient ell q c (k+1)=
      (((ell : ℂ)-2*q-2*k)*((ell : ℂ)-2*q+10-2*k)-
        ((ell*(ell+10) : ℕ) : ℂ))*spectralFreeSlowCoefficient ell q c k/
          (Complex.I*(k+1 : ℕ)) := by
  have hk : (k+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp only [spectralFreeSlowCoefficient,slowAsymptoticJet_succ_right,pow_succ,
    Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem spectralFreeSlowPolynomial_zero (ell : ℕ) (q c : ℂ) :
    spectralFreeSlowPolynomial ell q c 0=C c := by
  simp [spectralFreeSlowPolynomial,spectralFreeSlowCoefficient_zero,monomial_zero_left]

theorem spectralFreeSlowPolynomial_succ (ell : ℕ) (q c : ℂ) (j : ℕ) :
    spectralFreeSlowPolynomial ell q c (j+1)=spectralFreeSlowPolynomial ell q c j+
      monomial (j+1) (spectralFreeSlowCoefficient ell q c (j+1)) := by
  exact Finset.sum_range_succ _ _

theorem spectralFreeSlowPolynomial_degree (ell : ℕ) (q c : ℂ) (j : ℕ) :
    (spectralFreeSlowPolynomial ell q c j).natDegree ≤ j := by
  induction j with
  | zero => rw [spectralFreeSlowPolynomial_zero]; simp
  | succ j ih =>
    rw [spectralFreeSlowPolynomial_succ]
    exact (natDegree_add_le _ _).trans
      (max_le (ih.trans (Nat.le_succ j)) (natDegree_monomial_le _))

theorem spectralFreeSlowPolynomial_coefficient (ell : ℕ) (q c : ℂ) (j k : ℕ)
    (hk : k ≤ j) :
    (spectralFreeSlowPolynomial ell q c j).coeff k=spectralFreeSlowCoefficient ell q c k := by
  classical
  simp [spectralFreeSlowPolynomial,coeff_monomial,hk]

theorem spectralFreeSlowPolynomial_residual_top (ell : ℕ) (q c : ℂ) (j : ℕ) :
    (spectralPolynomialResidual 1 ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
      0 0 (spectralFreeSlowPolynomial ell q c j) 0).coeff j=
      (((ell : ℂ)-2*q-2*j)*((ell : ℂ)-2*q+10-2*j)-
        ((ell*(ell+10) : ℕ) : ℂ))*spectralFreeSlowCoefficient ell q c j := by
  have hz : (spectralFreeSlowPolynomial ell q c j).coeff (j+1)=0 :=
    coeff_eq_zero_of_natDegree_lt
      ((spectralFreeSlowPolynomial_degree ell q c j).trans_lt (Nat.lt_succ_self j))
  simp only [spectralPolynomialResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative,hz,zero_mul,mul_zero,sub_zero,
    spectralFreeSlowPolynomial_coefficient ell q c j j le_rfl]
  push_cast
  ring

theorem spectralOutgoingPolynomial_free_first (ell : ℕ) (q νm c : ℂ) (j : ℕ) :
    spectralOutgoingPolynomial ((ell : ℂ)-2*q) νm ((ell*(ell+10) : ℕ) : ℂ)
      1 0 (c,0) j=(spectralFreeSlowPolynomial ell q c j,0) := by
  induction j with
  | zero => simp [spectralOutgoingPolynomial,spectralFreeSlowPolynomial_zero]
  | succ j ih =>
    rw [spectralOutgoingPolynomial,ih]
    have hp : spectralDiagonalPolynomial 1 0=0 := by simp [spectralDiagonalPolynomial]
    have hc : spectralCrossPolynomial 1 0=0 := by simp [spectralCrossPolynomial]
    simp only [spectralPolynomialResidualPair,hp,hc,map_zero]
    rw [spectralFreeSlowPolynomial_residual_top,← spectralFreeSlowCoefficient_succ,
      ← spectralFreeSlowPolynomial_succ]
    simp [spectralPolynomialResidual,radialPolynomialEuler]

theorem spectralFreeSlowPolynomial_eval (ell : ℕ) (q c x z : ℂ) (j : ℕ)
    (hxz : (4*Complex.I*z)*x=1) :
    (spectralFreeSlowPolynomial ell q c j).eval z=
      c*slowAsymptoticPolynomial q (ell+6) j x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hxz
  have hi : x⁻¹=4*Complex.I*z := by
    have h := (div_eq_iff hx).mpr hxz.symm
    simpa only [one_div] using h
  simp only [spectralFreeSlowPolynomial,eval_finsetSum,eval_monomial,
    slowAsymptoticPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [spectralFreeSlowCoefficient,Complex.real_smul,Complex.ofReal_inv,
    Complex.ofReal_natCast,div_eq_mul_inv,← inv_pow,hi,mul_pow]
  ring

end DefocusingNLS

end OAI
