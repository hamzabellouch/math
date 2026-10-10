import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSlowJet
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSlowPolynomial
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowAsymptotic
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorJetLimit

namespace OAI

/-! Actual remainder estimates for the free angular H columns. -/

open Polynomial
namespace DefocusingNLS

theorem spectralFreeSlowPolynomial_euler_shift (ell : ℕ) (q c : ℂ) (j : ℕ) :
    radialPolynomialEuler (spectralFreeSlowPolynomial ell q c (j+1))=
      C (-8*Complex.I*c*q*((ell : ℂ)+5-q))*
        (X*spectralFreeSlowPolynomial ell (q+1) 1 j) := by
  ext k
  rw [radialPolynomialEuler_coeff,coeff_C_mul]
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul]
    by_cases hk : k ≤ j
    · rw [spectralFreeSlowPolynomial_coefficient _ _ _ _ _ (Nat.succ_le_succ hk),
        spectralFreeSlowPolynomial_coefficient _ _ _ _ _ hk]
      simp only [spectralFreeSlowCoefficient,slowAsymptoticJet,
        Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,pow_succ]
      field_simp
      ring
    · have hk' : j < k := Nat.lt_of_not_ge hk
      rw [coeff_eq_zero_of_natDegree_lt ((spectralFreeSlowPolynomial_degree _ _ _ _).trans_lt
          (Nat.succ_lt_succ hk')),
        coeff_eq_zero_of_natDegree_lt ((spectralFreeSlowPolynomial_degree _ _ _ _).trans_lt hk'),
        mul_zero,mul_zero]

theorem spectralFreeSlowValue_remainder (ell : ℕ) (q : ℂ) (hq : -1 < q.re) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, Real.log 4/2 ≤ t →
      ‖(spectralFreeSlowJet q (ell+6) t).1-
        radialExteriorPolynomialFunction (spectralFreeSlowPolynomial ell q 1 j) t‖ ≤
          C*Real.exp (-(2*((j+1 : ℕ) : ℝ))*t) := by
  obtain ⟨A,hA,hb⟩ := regularizedSlowSolution_allOrders_remainder j q (ell+6) hq
  refine ⟨A*4^(j+1),by positivity,?_⟩
  intro t ht
  have he := spectralFreeSlowPolynomial_eval ell q 1 (radialFreeSlowArgument t)
    (Real.exp (-2*t) : ℂ) j (radialFreeSlowArgument_reciprocal t)
  change ‖normalizedSlowSolution q (ell+6) (radialFreeSlowArgument t)-
    (spectralFreeSlowPolynomial ell q 1 j).eval (Real.exp (-2*t) : ℂ)‖ ≤ _
  rw [he,one_mul]
  calc
    _ ≤ A/‖radialFreeSlowArgument t‖^(j+1) :=
      hb _ (by rw [radialFreeSlowArgument_re]) (radialFreeSlowArgument_large t ht)
    _ = _ := by rw [div_eq_mul_one_div,radialFreeSlowArgument_inverse_power]; ring

theorem spectralFreeSlowVelocity_remainder (ell : ℕ) (q : ℂ) (hq : -1 < q.re) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, Real.log 4/2 ≤ t →
      ‖(spectralFreeSlowJet q (ell+6) t).2-
        radialExteriorPolynomialFunction
          (radialPolynomialEuler (spectralFreeSlowPolynomial ell q 1 (j+1))) t‖ ≤
          C*Real.exp (-(2*((j+2 : ℕ) : ℝ))*t) := by
  have hq1 : -1 < (q+1).re := by change -1 < q.re+1; linarith
  obtain ⟨A,hA,hb⟩ := regularizedSlowSolution_allOrders_remainder j (q+1) (ell+6) hq1
  let c : ℂ := -2*q*((ell : ℂ)+5-q)
  refine ⟨‖c‖*A*4^(j+2),by positivity,?_⟩
  intro t ht
  let x := radialFreeSlowArgument t
  have hx : x ≠ 0 := radialFreeSlowArgument_ne_zero t
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hv : (spectralFreeSlowJet q (ell+6) t).2=
      c/x*normalizedSlowSolution (q+1) (ell+6) x := by
    rw [spectralFreeSlowJet,normalizedSlowFirst_eq_shift q (ell+6) _ hq
      (by rw [radialFreeSlowArgument_re]) hx]
    dsimp only [c,x]
    push_cast
    field_simp
    ring
  have hrec : 4*Complex.I*(Real.exp (-2*t) : ℂ)=1/x :=
    (eq_div_iff hx).mpr (radialFreeSlowArgument_reciprocal t)
  have hp : radialExteriorPolynomialFunction
      (radialPolynomialEuler (spectralFreeSlowPolynomial ell q 1 (j+1))) t=
      c/x*slowAsymptoticPolynomial (q+1) (ell+6) j x := by
    rw [radialExteriorPolynomialFunction,spectralFreeSlowPolynomial_euler_shift,
      eval_mul,eval_C,eval_mul,eval_X,spectralFreeSlowPolynomial_eval ell (q+1) 1 x _ j
        (radialFreeSlowArgument_reciprocal t),one_mul]
    calc
      _ = c*(4*Complex.I*(Real.exp (-2*t) : ℂ))*
          slowAsymptoticPolynomial (q+1) (ell+6) j x := by dsimp [c]; ring
      _ = _ := by rw [hrec]; ring
  rw [hv,hp,← mul_sub,norm_mul,norm_div]
  calc
    _ ≤ (‖c‖/‖x‖)*(A/‖x‖^(j+1)) :=
      mul_le_mul_of_nonneg_left (hb x (by rw [radialFreeSlowArgument_re])
        (radialFreeSlowArgument_large t ht)) (by positivity)
    _ = (‖c‖*A)*(1/‖x‖^(j+2)) := by
      rw [show j+2=(j+1)+1 by omega,pow_succ]
      field_simp
      ring
    _ = _ := by rw [radialFreeSlowArgument_inverse_power]; ring

theorem spectralFreeSlowJet_remainder (ell : ℕ) (q : ℂ) (hq : -1 < q.re) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, Real.log 4/2 ≤ t →
      ‖spectralFreeSlowJet q (ell+6) t-
        radialPolynomialJet (spectralFreeSlowPolynomial ell q 1 (j+1)) t‖ ≤
          C*Real.exp (-(2*((j+2 : ℕ) : ℝ))*t) := by
  obtain ⟨A,hA,hv⟩ := spectralFreeSlowValue_remainder ell q hq (j+1)
  obtain ⟨B,hB,hw⟩ := spectralFreeSlowVelocity_remainder ell q hq j
  refine ⟨max A B,le_max_of_le_left hA,?_⟩
  intro t ht
  change max ‖(spectralFreeSlowJet q (ell+6) t).1-
      radialExteriorPolynomialFunction _ t‖
    ‖(spectralFreeSlowJet q (ell+6) t).2-radialExteriorPolynomialFunction _ t‖ ≤ _
  exact max_le
    ((hv t ht).trans (mul_le_mul_of_nonneg_right (le_max_left A B) (Real.exp_nonneg _)))
    ((hw t ht).trans (mul_le_mul_of_nonneg_right (le_max_right A B) (Real.exp_nonneg _)))

end DefocusingNLS

end OAI
