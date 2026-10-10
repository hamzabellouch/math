import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialResidual

namespace OAI

/-! The two normalized slow polynomial columns for the actual odd-power coefficients. -/

open Polynomial
namespace DefocusingNLS

noncomputable def spectralDiagonalPolynomial (m : ℕ) (P : ℂ[X]) : ℂ[X] :=
  C ((m+1 : ℕ) : ℂ)*P^m*(Polynomial.mapRingHom (starRingEnd ℂ) P)^m

noncomputable def spectralCrossPolynomial (m : ℕ) (P : ℂ[X]) : ℂ[X] :=
  C (m : ℂ)*P^(m+1)*(Polynomial.mapRingHom (starRingEnd ℂ) P)^(m-1)

noncomputable def spectralPolynomialResidualPair (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (U : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  (spectralPolynomialResidual 1 νp η (spectralDiagonalPolynomial m P)
      (spectralCrossPolynomial m P) U.1 U.2,
   spectralPolynomialResidual (-1) νm η
      (Polynomial.mapRingHom (starRingEnd ℂ) (spectralDiagonalPolynomial m P))
      (Polynomial.mapRingHom (starRingEnd ℂ) (spectralCrossPolynomial m P)) U.2 U.1)

noncomputable def spectralOutgoingPolynomial (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) : ℕ → ℂ[X] × ℂ[X]
  | 0 => (C c.1,C c.2)
  | j+1 =>
    let U := spectralOutgoingPolynomial νp νm η m P c j
    let R := spectralPolynomialResidualPair νp νm η m P U
    (U.1+monomial (j+1) (R.1.coeff j/(Complex.I*(j+1 : ℕ))),
     U.2+monomial (j+1) (R.2.coeff j/(-Complex.I*(j+1 : ℕ))))

theorem spectralOutgoingPolynomial_constant (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) :
    (spectralOutgoingPolynomial νp νm η m P c j).1.coeff 0=c.1 ∧
      (spectralOutgoingPolynomial νp νm η m P c j).2.coeff 0=c.2 := by
  induction j with
  | zero => simp [spectralOutgoingPolynomial]
  | succ j ih => simpa [spectralOutgoingPolynomial] using ih

theorem spectralOutgoingPolynomial_degree (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) :
    (spectralOutgoingPolynomial νp νm η m P c j).1.natDegree ≤ j ∧
      (spectralOutgoingPolynomial νp νm η m P c j).2.natDegree ≤ j := by
  induction j with
  | zero => simp [spectralOutgoingPolynomial]
  | succ j ih =>
    constructor
    · exact (natDegree_add_le _ _).trans
        (max_le (ih.1.trans (Nat.le_succ j)) (natDegree_monomial_le _))
    · exact (natDegree_add_le _ _).trans
        (max_le (ih.2.trans (Nat.le_succ j)) (natDegree_monomial_le _))

theorem spectralOutgoingPolynomial_residual (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) :
    X^j ∣ (spectralPolynomialResidualPair νp νm η m P
      (spectralOutgoingPolynomial νp νm η m P c j)).1 ∧
    X^j ∣ (spectralPolynomialResidualPair νp νm η m P
      (spectralOutgoingPolynomial νp νm η m P c j)).2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : (j+1 : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero j
    constructor
    · apply X_pow_dvd_iff.mpr
      intro k hk
      have hkj : k ≤ j := by omega
      change (spectralPolynomialResidual 1 νp η _ _ _ _).coeff k=0
      rw [spectralOutgoingPolynomial]
      rw [spectralPolynomialResidual_update _ _ _ _ _ _ _ j k _ _ hkj]
      by_cases he : k=j
      · subst k
        simp only [ite_true,one_mul]
        change (spectralPolynomialResidualPair νp νm η m P
          (spectralOutgoingPolynomial νp νm η m P c j)).1.coeff j-
          Complex.I*((j+1 : ℕ)*((spectralPolynomialResidualPair νp νm η m P
            (spectralOutgoingPolynomial νp νm η m P c j)).1.coeff j/(Complex.I*(j+1 : ℕ))))=0
        field_simp [Complex.I_ne_zero,hj]
        ring
      · simp only [he,ite_false,sub_zero]
        exact X_pow_dvd_iff.mp ih.1 k (by omega)
    · apply X_pow_dvd_iff.mpr
      intro k hk
      have hkj : k ≤ j := by omega
      change (spectralPolynomialResidual (-1) νm η _ _ _ _).coeff k=0
      rw [spectralOutgoingPolynomial]
      rw [spectralPolynomialResidual_update _ _ _ _ _ _ _ j k _ _ hkj]
      by_cases he : k=j
      · subst k
        simp only [ite_true,neg_one_mul]
        change (spectralPolynomialResidualPair νp νm η m P
          (spectralOutgoingPolynomial νp νm η m P c j)).2.coeff j-
          -Complex.I*((j+1 : ℕ)*((spectralPolynomialResidualPair νp νm η m P
            (spectralOutgoingPolynomial νp νm η m P c j)).2.coeff j/(-Complex.I*(j+1 : ℕ))))=0
        field_simp [Complex.I_ne_zero,hj]
        ring
      · simp only [he,ite_false,sub_zero]
        exact X_pow_dvd_iff.mp ih.2 k (by omega)

end DefocusingNLS

end OAI
