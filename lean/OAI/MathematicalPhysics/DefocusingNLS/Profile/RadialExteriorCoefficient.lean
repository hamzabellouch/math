import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansion

namespace OAI

/-! The explicit triangular recurrence for the exterior coefficients. -/

open Polynomial
namespace DefocusingNLS

theorem radialExteriorPolynomialResidual_top (ν : ℂ) (n j : ℕ) (P : ℂ[X])
    (hP : P.natDegree ≤ j) :
    (radialExteriorPolynomialResidual ν n P).coeff j =
      (ν-2*(j : ℂ))*(ν+10-2*(j : ℂ))*P.coeff j-
        (radialPolynomialPower n P).coeff j := by
  have hz : P.coeff (j+1)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp only [radialExteriorPolynomialResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative,hz,zero_mul,mul_zero,sub_zero]
  ring

theorem radialExteriorExpansion_step (ν : ℂ) (n : ℕ) (m : ℂ) (j : ℕ) :
    radialExteriorExpansion ν n m (j+1) =
      radialExteriorExpansion ν n m j+monomial (j+1)
        (((ν-2*(j : ℂ))*(ν+10-2*(j : ℂ))*(radialExteriorExpansion ν n m j).coeff j-
          (radialPolynomialPower n (radialExteriorExpansion ν n m j)).coeff j) /
          (Complex.I*(j+1 : ℕ))) := by
  rw [radialExteriorExpansion,radialExteriorPolynomialResidual_top ν n j _
    (radialExteriorExpansion_degree ν n m j)]

noncomputable def radialFreeExpansion (ν m : ℂ) : ℕ → ℂ[X]
  | 0 => C m
  | j+1 => let P := radialFreeExpansion ν m j
    P+monomial (j+1) ((ν-2*(j : ℂ))*(ν+10-2*(j : ℂ))*P.coeff j /
      (Complex.I*(j+1 : ℕ)))

theorem radialFreeExpansion_constant (ν m : ℂ) (j : ℕ) :
    (radialFreeExpansion ν m j).coeff 0=m := by
  induction j with
  | zero => simp [radialFreeExpansion]
  | succ j ih => simp [radialFreeExpansion,ih]

theorem radialFreeExpansion_degree (ν m : ℂ) (j : ℕ) :
    (radialFreeExpansion ν m j).natDegree ≤ j := by
  induction j with
  | zero => simp [radialFreeExpansion]
  | succ j ih =>
    exact (natDegree_add_le _ _).trans (max_le (ih.trans (Nat.le_succ j))
      (natDegree_monomial_le _))

end DefocusingNLS

end OAI
