import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreePochhammer

namespace OAI

/-! The velocity expansion agrees with the differentiated outgoing H expansion. -/

open Polynomial
namespace DefocusingNLS

theorem radialFreeExpansion_euler_shift (q m : ℂ) (j : ℕ) :
    radialPolynomialEuler (radialFreeExpansion (-2*q) m (j+1))=
      C (-8*Complex.I*m*q*(5-q))*(X*radialFreeExpansion (-2*(q+1)) 1 j) := by
  ext k
  rw [radialPolynomialEuler_coeff,coeff_C_mul]
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul]
    by_cases hk : k ≤ j
    · rw [radialFreeExpansion_coefficient _ _ _ _ (Nat.succ_le_succ hk),
        radialFreeExpansion_coefficient _ _ _ _ hk]
      have hq : -(-2*q)/2=q := by ring
      have hq' : -(-2*(q+1))/2=q+1 := by ring
      simp only [radialFreePochhammerCoefficient,hq,hq',slowAsymptoticJet,
        Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,pow_succ]
      field_simp
      ring
    · have hk' : j < k := Nat.lt_of_not_ge hk
      rw [coeff_eq_zero_of_natDegree_lt ((radialFreeExpansion_degree _ _ _).trans_lt
          (Nat.succ_lt_succ hk')),
        coeff_eq_zero_of_natDegree_lt ((radialFreeExpansion_degree _ _ _).trans_lt hk'),
        mul_zero,mul_zero]

theorem radialFreeExpansion_euler_eval_slowAsymptotic (q m x z : ℂ) (j : ℕ)
    (hxz : (4*Complex.I*z)*x=1) :
    (radialPolynomialEuler (radialFreeExpansion (-2*q) m (j+1))).eval z=
      -8*Complex.I*m*q*(5-q)*z*slowAsymptoticPolynomial (q+1) 6 j x := by
  rw [radialFreeExpansion_euler_shift,eval_mul,eval_C,eval_mul,eval_X,
    radialFreeExpansion_eval_slowAsymptotic _ _ _ _ _ hxz]
  have hq' : -(-2*(q+1))/2=q+1 := by ring
  rw [hq']
  ring

end DefocusingNLS

end OAI
