import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPolynomial

namespace OAI

/-! The triangular exterior coefficient construction and its exact residual order. -/

open Polynomial
namespace DefocusingNLS

noncomputable def radialExteriorExpansion (ν : ℂ) (n : ℕ) (m : ℂ) : ℕ → ℂ[X]
  | 0 => C m
  | j+1 => let P := radialExteriorExpansion ν n m j
    P+monomial (j+1) ((radialExteriorPolynomialResidual ν n P).coeff j /
      (Complex.I*(j+1 : ℕ)))

theorem radialExteriorExpansion_constant (ν : ℂ) (n : ℕ) (m : ℂ) (j : ℕ) :
    (radialExteriorExpansion ν n m j).coeff 0=m := by
  induction j with
  | zero => simp [radialExteriorExpansion]
  | succ j ih => simp [radialExteriorExpansion,ih]

theorem radialExteriorExpansion_degree (ν : ℂ) (n : ℕ) (m : ℂ) (j : ℕ) :
    (radialExteriorExpansion ν n m j).natDegree ≤ j := by
  induction j with
  | zero => simp [radialExteriorExpansion]
  | succ j ih =>
    exact (natDegree_add_le _ _).trans (max_le (ih.trans (Nat.le_succ j))
      (natDegree_monomial_le _))

theorem radialExteriorExpansion_residual (ν : ℂ) (n : ℕ) (m : ℂ) (j : ℕ) :
    X^j ∣ radialExteriorPolynomialResidual ν n (radialExteriorExpansion ν n m j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    apply X_pow_dvd_iff.mpr
    intro k hk
    have hkj : k ≤ j := by omega
    rw [radialExteriorExpansion,radialExteriorPolynomialResidual_update ν n j k _ _ hkj]
    by_cases he : k=j
    · subst k
      simp only [ite_true]
      have hj : (j+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have hi : Complex.I ≠ 0 := Complex.I_ne_zero
      field_simp
      ring
    · simp only [he,ite_false,sub_zero]
      exact X_pow_dvd_iff.mp ih k (by omega)

theorem radialExteriorExpansion_coeff_stable (ν : ℂ) (n : ℕ) (m : ℂ) (j k : ℕ)
    (hk : k ≤ j) :
    (radialExteriorExpansion ν n m (j+1)).coeff k=(radialExteriorExpansion ν n m j).coeff k := by
  have hne : j+1 ≠ k := by omega
  simp [radialExteriorExpansion,coeff_add,coeff_monomial,hne]

end DefocusingNLS

end OAI
