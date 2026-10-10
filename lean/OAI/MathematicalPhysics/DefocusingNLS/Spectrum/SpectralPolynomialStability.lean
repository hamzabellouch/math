import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialExpansion

namespace OAI

/-! Finite spectral coefficients depend only on the matching finite profile jet. -/

open Polynomial
namespace DefocusingNLS

private theorem polynomial_mul_difference_dvd (D A B C E : ℂ[X])
    (hAB : D ∣ A-B) (hCE : D ∣ C-E) : D ∣ A*C-B*E := by
  have h := dvd_add (dvd_mul_of_dvd_left hAB C) (dvd_mul_of_dvd_right hCE B)
  convert h using 1
  ring

theorem spectralPolynomial_star_difference_dvd (P Q : ℂ[X]) (j : ℕ)
    (h : X^j ∣ P-Q) :
    X^j ∣ Polynomial.mapRingHom (starRingEnd ℂ) P-
      Polynomial.mapRingHom (starRingEnd ℂ) Q := by
  have hm := Polynomial.map_dvd (starRingEnd ℂ) h
  simpa only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,
    Polynomial.coe_mapRingHom] using hm

theorem spectralPolynomial_coefficients_difference_dvd (m : ℕ) (P Q : ℂ[X]) (j : ℕ)
    (h : X^j ∣ P-Q) :
    X^j ∣ spectralDiagonalPolynomial m P-spectralDiagonalPolynomial m Q ∧
    X^j ∣ spectralCrossPolynomial m P-spectralCrossPolynomial m Q := by
  have hp (k : ℕ) : X^j ∣ P^k-Q^k := h.trans (sub_dvd_pow_sub_pow P Q k)
  have hs := spectralPolynomial_star_difference_dvd P Q j h
  have hsp (k : ℕ) : X^j ∣
      (Polynomial.mapRingHom (starRingEnd ℂ) P)^k-
      (Polynomial.mapRingHom (starRingEnd ℂ) Q)^k :=
    hs.trans (sub_dvd_pow_sub_pow _ _ k)
  constructor
  · unfold spectralDiagonalPolynomial
    rw [mul_assoc,mul_assoc,← mul_sub]
    exact dvd_mul_of_dvd_right (polynomial_mul_difference_dvd _ _ _ _ _ (hp m) (hsp m)) _
  · unfold spectralCrossPolynomial
    rw [mul_assoc,mul_assoc,← mul_sub]
    exact dvd_mul_of_dvd_right
      (polynomial_mul_difference_dvd _ _ _ _ _ (hp (m+1)) (hsp (m-1))) _

theorem spectralPolynomialResidual_coefficient_change (h ν η : ℂ)
    (A B A' B' U V : ℂ[X]) (j k : ℕ) (hkj : k < j)
    (hA : X^j ∣ A'-A) (hB : X^j ∣ B'-B) :
    (spectralPolynomialResidual h ν η A' B' U V).coeff k=
      (spectralPolynomialResidual h ν η A B U V).coeff k := by
  have hAU := (X_pow_dvd_iff.mp (dvd_mul_of_dvd_left hA U)) k hkj
  have hBV := (X_pow_dvd_iff.mp (dvd_mul_of_dvd_left hB V)) k hkj
  have heA : (A'*U).coeff k=(A*U).coeff k := by
    rw [sub_mul,coeff_sub] at hAU
    exact sub_eq_zero.mp hAU
  have heB : (B'*V).coeff k=(B*V).coeff k := by
    rw [sub_mul,coeff_sub] at hBV
    exact sub_eq_zero.mp hBV
  simp only [spectralPolynomialResidual,coeff_sub,heA,heB]

theorem spectralOutgoingPolynomial_coeff_stable (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j k : ℕ) (hk : k ≤ j) :
    (spectralOutgoingPolynomial νp νm η m P c (j+1)).1.coeff k=
      (spectralOutgoingPolynomial νp νm η m P c j).1.coeff k ∧
    (spectralOutgoingPolynomial νp νm η m P c (j+1)).2.coeff k=
      (spectralOutgoingPolynomial νp νm η m P c j).2.coeff k := by
  have hne : j+1 ≠ k := by omega
  simp [spectralOutgoingPolynomial,coeff_monomial,hne]

theorem spectralOutgoingPolynomial_profile_jet (νp νm η : ℂ) (m : ℕ)
    (P Q : ℂ[X]) (c : ℂ × ℂ) (J i : ℕ) (hi : i ≤ J)
    (hPQ : X^J ∣ P-Q) :
    spectralOutgoingPolynomial νp νm η m P c i=
      spectralOutgoingPolynomial νp νm η m Q c i := by
  obtain ⟨hA,hB⟩ := spectralPolynomial_coefficients_difference_dvd m P Q J hPQ
  have hsA := spectralPolynomial_star_difference_dvd
    (spectralDiagonalPolynomial m P) (spectralDiagonalPolynomial m Q) J hA
  have hsB := spectralPolynomial_star_difference_dvd
    (spectralCrossPolynomial m P) (spectralCrossPolynomial m Q) J hB
  induction i with
  | zero => rfl
  | succ i ih =>
    have hiJ : i < J := by omega
    have he := ih (by omega)
    let U := spectralOutgoingPolynomial νp νm η m Q c i
    have hp : (spectralPolynomialResidualPair νp νm η m P U).1.coeff i=
        (spectralPolynomialResidualPair νp νm η m Q U).1.coeff i :=
      spectralPolynomialResidual_coefficient_change 1 νp η _ _ _ _ U.1 U.2 J i hiJ hA hB
    have hm : (spectralPolynomialResidualPair νp νm η m P U).2.coeff i=
        (spectralPolynomialResidualPair νp νm η m Q U).2.coeff i :=
      spectralPolynomialResidual_coefficient_change (-1) νm η _ _ _ _ U.2 U.1 J i hiJ hsA hsB
    simp only [spectralOutgoingPolynomial,he]
    change (U.1+_,U.2+_)=(U.1+_,U.2+_)
    rw [hp,hm]

theorem spectralOutgoingPolynomial_coeff_initial (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j k i : ℕ) (hjk : j ≤ k) (hi : i ≤ j) :
    (spectralOutgoingPolynomial νp νm η m P c k).1.coeff i=
      (spectralOutgoingPolynomial νp νm η m P c j).1.coeff i ∧
    (spectralOutgoingPolynomial νp νm η m P c k).2.coeff i=
      (spectralOutgoingPolynomial νp νm η m P c j).2.coeff i := by
  induction k with
  | zero =>
    have hj : j=0 := by omega
    subst j
    exact ⟨rfl,rfl⟩
  | succ k ih =>
    by_cases hj : j=k+1
    · subst j; exact ⟨rfl,rfl⟩
    · have hjk' : j ≤ k := by omega
      have hs := spectralOutgoingPolynomial_coeff_stable νp νm η m P c k i (hi.trans hjk')
      have hh := ih hjk'
      exact ⟨hs.1.trans hh.1,hs.2.trans hh.2⟩

theorem spectralOutgoingPolynomial_order_difference (νp νm η : ℂ) (m : ℕ)
    (P Q : ℂ[X]) (c : ℂ × ℂ) (j k : ℕ) (hjk : j ≤ k)
    (hPQ : X^j ∣ P-Q) :
    X^(j+1) ∣ (spectralOutgoingPolynomial νp νm η m Q c k).1-
      (spectralOutgoingPolynomial νp νm η m P c j).1 ∧
    X^(j+1) ∣ (spectralOutgoingPolynomial νp νm η m Q c k).2-
      (spectralOutgoingPolynomial νp νm η m P c j).2 := by
  have he := spectralOutgoingPolynomial_profile_jet νp νm η m P Q c j j le_rfl hPQ
  rw [he]
  constructor
  · apply X_pow_dvd_iff.mpr
    intro i hi
    rw [coeff_sub,(spectralOutgoingPolynomial_coeff_initial νp νm η m Q c j k i hjk
      (by omega)).1,sub_self]
  · apply X_pow_dvd_iff.mpr
    intro i hi
    rw [coeff_sub,(spectralOutgoingPolynomial_coeff_initial νp νm η m Q c j k i hjk
      (by omega)).2,sub_self]

end DefocusingNLS

end OAI
