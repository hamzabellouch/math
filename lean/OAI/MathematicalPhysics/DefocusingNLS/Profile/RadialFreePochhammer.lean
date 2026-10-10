import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCoefficient
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowAsymptoticCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowAllOrdersAsymptotic

namespace OAI

/-! Identify the free exterior coefficients with the actual outgoing H expansion. -/

open Polynomial
namespace DefocusingNLS

theorem slowAsymptoticJet_succ_right (q : ℂ) (M k : ℕ) :
    slowAsymptoticJet q M (k+1)=
      (q+k)*((M : ℂ)-1-q-k)*slowAsymptoticJet q M k := by
  rw [slowAsymptoticJet_eq_pochhammer,ascPochhammer_succ_right,descPochhammer_succ_right,
    slowAsymptoticJet_eq_pochhammer]
  simp only [eval_mul,eval_add,eval_sub,eval_X,eval_natCast]
  ring

noncomputable def radialFreePochhammerCoefficient (ν m : ℂ) (k : ℕ) : ℂ :=
  m*(4*Complex.I)^k*slowAsymptoticJet (-ν/2) 6 k/(k.factorial : ℂ)

theorem radialFreePochhammerCoefficient_zero (ν m : ℂ) :
    radialFreePochhammerCoefficient ν m 0=m := by
  simp [radialFreePochhammerCoefficient,slowAsymptoticJet]

theorem radialFreePochhammerCoefficient_succ (ν m : ℂ) (k : ℕ) :
    radialFreePochhammerCoefficient ν m (k+1)=
      (ν-2*(k : ℂ))*(ν+10-2*(k : ℂ))*radialFreePochhammerCoefficient ν m k/
        (Complex.I*(k+1 : ℕ)) := by
  have hk : (k+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp only [radialFreePochhammerCoefficient,slowAsymptoticJet_succ_right,pow_succ,Nat.factorial_succ,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem radialFreeExpansion_topCoefficient (ν m : ℂ) (j : ℕ) :
    (radialFreeExpansion ν m j).coeff j=radialFreePochhammerCoefficient ν m j := by
  induction j with
  | zero => simp [radialFreeExpansion,radialFreePochhammerCoefficient_zero]
  | succ j ih =>
    have hz : (radialFreeExpansion ν m j).coeff (j+1)=0 :=
      coeff_eq_zero_of_natDegree_lt ((radialFreeExpansion_degree ν m j).trans_lt (Nat.lt_succ_self _))
    simp only [radialFreeExpansion,coeff_add,coeff_monomial,ite_true,hz,zero_add,ih]
    exact (radialFreePochhammerCoefficient_succ ν m j).symm

theorem radialFreeExpansion_coefficient (ν m : ℂ) (j k : ℕ) (hk : k ≤ j) :
    (radialFreeExpansion ν m j).coeff k=radialFreePochhammerCoefficient ν m k := by
  induction j with
  | zero =>
    have h := Nat.eq_zero_of_le_zero hk
    subst k
    exact radialFreeExpansion_topCoefficient ν m 0
  | succ j ih =>
    by_cases he : k=j+1
    · subst k
      exact radialFreeExpansion_topCoefficient ν m (j+1)
    · have hkj : k ≤ j := by omega
      have hne : j+1 ≠ k := Ne.symm he
      simp only [radialFreeExpansion,coeff_add,coeff_monomial,hne,ite_false,add_zero]
      exact ih hkj

theorem radialFreeExpansion_eval_slowAsymptotic (ν m x z : ℂ) (j : ℕ)
    (hxz : (4*Complex.I*z)*x=1) :
    (radialFreeExpansion ν m j).eval z=m*slowAsymptoticPolynomial (-ν/2) 6 j x := by
  have hx : x ≠ 0 := by intro h; simp [h] at hxz
  have hi : x⁻¹=4*Complex.I*z := by
    have h := (div_eq_iff hx).mpr hxz.symm
    simpa only [one_div] using h
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le (radialFreeExpansion_degree ν m j)) z,
    slowAsymptoticPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [radialFreeExpansion_coefficient ν m j k (by have := Finset.mem_range.mp hk; omega)]
  simp only [radialFreePochhammerCoefficient,Complex.real_smul,Complex.ofReal_inv,
    Complex.ofReal_natCast,div_eq_mul_inv,← inv_pow,hi,mul_pow]
  ring

end DefocusingNLS

end OAI
