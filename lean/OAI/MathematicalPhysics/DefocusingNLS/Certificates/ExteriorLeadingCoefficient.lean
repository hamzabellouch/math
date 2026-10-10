import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorPolynomialDegree

namespace OAI

/-! The two leading column coefficients needed for the imaginary-part cancellation. -/

open Polynomial Matrix
namespace DefocusingNLS.ExteriorCertificate
open BoundaryCertificate (stateMatrix polynomialStep)

theorem coeff_inputS_mul (z₀ : ℤ) (p : Polynomial ℂ) (n : ℕ) :
    (inputS z₀*p).coeff (n+1) = Complex.I*(z₀ : ℂ)*p.coeff (n+1)+
      (Complex.I*(100000000 : ℂ))*p.coeff n := by
  simp only [inputS,add_mul,mul_assoc,coeff_add,coeff_C_mul,coeff_X_mul]

noncomputable def firstLeading (b : ℝ) : Fin 2 → ℂ :=
  ![-Complex.I*(100000000 : ℂ)*(b : ℂ),Complex.I*(100000000 : ℂ)]

theorem state_leading (z₀ : ℤ) (b : ℝ) (n : ℕ) (j : Fin 2) :
    (stateMatrix (polynomialState z₀ b (n+1)) 0 j).coeff (n+j.val) =
        (-Complex.I*(100000000 : ℂ))^n*firstLeading b j ∧
    (stateMatrix (polynomialState z₀ b (n+1)) 1 j).coeff (n+j.val) =
        -((-Complex.I*(100000000 : ℂ))^n*firstLeading b j) := by
  induction n with
  | zero =>
    fin_cases j <;>
      simp [polynomialState,polynomialStep,stateMatrix,inputT,inputS,firstLeading]
    ring
  | succ n ih =>
    have hz (i : Fin 2) :
        (stateMatrix (polynomialState z₀ b (n+1)) i j).coeff ((n+j.val)+1) = 0 :=
      coeff_eq_zero_of_natDegree_lt ((state_column_degree z₀ b n i j).trans_lt
        (Nat.lt_succ_self _))
    have hx : (stateMatrix (polynomialState z₀ b ((n+1)+1)) 0 j).coeff ((n+j.val)+1) =
        (Complex.I*(100000000 : ℂ))*
          (stateMatrix (polynomialState z₀ b (n+1)) 1 j).coeff (n+j.val) := by
      rw [state_entry_succ_zero,coeff_add,coeff_inputS_mul]
      simp only [inputT,coeff_C_mul,hz,mul_zero,zero_add]
    have he : (n+1)+j.val = (n+j.val)+1 := by omega
    constructor
    · rw [he,hx,ih.2,pow_succ]
      ring
    · rw [he,state_entry_succ_one,sub_mul,coeff_sub,coeff_sub]
      simp only [inputT,coeff_C_mul,hz,mul_zero,sub_self,zero_sub]
      rw [hx,ih.2,pow_succ]
      ring

end DefocusingNLS.ExteriorCertificate

end OAI
