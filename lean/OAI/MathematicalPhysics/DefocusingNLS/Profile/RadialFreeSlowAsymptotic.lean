import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeEulerExpansion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansionEquation

namespace OAI

/-! Quantitative value and velocity expansions of the actual outgoing H profile. -/

namespace DefocusingNLS

theorem radialFreeSlowArgument_norm (t : ℝ) :
    ‖radialFreeSlowArgument t‖=Real.exp (2*t)/4 := by
  simp only [radialFreeSlowArgument,norm_neg,norm_mul,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs]
  exact abs_of_pos (by positivity)

theorem radialFreeSlowArgument_reciprocal (t : ℝ) :
    (4*Complex.I*(Real.exp (-2*t) : ℂ))*radialFreeSlowArgument t=1 := by
  have he : Real.exp (-2*t)*Real.exp (2*t)=1 := by
    rw [← Real.exp_add]
    simp
  have hec : (Real.exp (-2*t) : ℂ)*(Real.exp (2*t) : ℂ)=1 := by exact_mod_cast he
  simp only [radialFreeSlowArgument,Complex.ofReal_div,Complex.ofReal_ofNat]
  linear_combination -Complex.I^2*hec - Complex.I_sq

theorem radialFreeSlowArgument_large (t : ℝ) (ht : Real.log 4/2 ≤ t) :
    1 ≤ ‖radialFreeSlowArgument t‖ := by
  rw [radialFreeSlowArgument_norm]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have h := Real.exp_le_exp.mpr (show Real.log 4 ≤ 2*t by linarith)
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4),one_mul] using h

theorem radialFreeSlowArgument_inverse_power (t : ℝ) (k : ℕ) :
    1/‖radialFreeSlowArgument t‖^k=4^k*Real.exp (-(2*(k : ℝ))*t) := by
  rw [radialFreeSlowArgument_norm,div_pow,one_div_div,← Real.exp_nat_mul]
  rw [div_eq_mul_inv,← Real.exp_neg]
  congr 2
  ring

theorem radialFreeSlowValue_remainder (q m : ℂ) (hq : -1 < q.re) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, Real.log 4/2 ≤ t →
      ‖radialFreeSlowValue q m t-
        radialExteriorPolynomialFunction (radialFreeExpansion (-2*q) m j) t‖ ≤
          C*Real.exp (-(2*((j+1 : ℕ) : ℝ))*t) := by
  obtain ⟨A,hA,hb⟩ := regularizedSlowSolution_allOrders_remainder j q 6 hq
  refine ⟨‖m‖*A*4^(j+1),by positivity,?_⟩
  intro t ht
  have hq' : -(-2*q)/2=q := by ring
  have he := radialFreeExpansion_eval_slowAsymptotic (-2*q) m
    (radialFreeSlowArgument t) (Real.exp (-2*t) : ℂ) j (radialFreeSlowArgument_reciprocal t)
  rw [hq'] at he
  change ‖m*normalizedSlowSolution q 6 (radialFreeSlowArgument t)-
    (radialFreeExpansion (-2*q) m j).eval (Real.exp (-2*t) : ℂ)‖ ≤ _
  rw [he,← mul_sub,norm_mul]
  calc
    _ ≤ ‖m‖*(A/‖radialFreeSlowArgument t‖^(j+1)) :=
      mul_le_mul_of_nonneg_left (hb _ (by rw [radialFreeSlowArgument_re])
        (radialFreeSlowArgument_large t ht)) (norm_nonneg _)
    _ = _ := by rw [div_eq_mul_one_div,radialFreeSlowArgument_inverse_power]; ring

theorem radialFreeSlowVelocity_remainder (q m : ℂ) (hq : -1 < q.re) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, Real.log 4/2 ≤ t →
      ‖radialFreeSlowVelocity q m t-
        radialExteriorPolynomialFunction (radialPolynomialEuler
          (radialFreeExpansion (-2*q) m (j+1))) t‖ ≤
          C*Real.exp (-(2*((j+2 : ℕ) : ℝ))*t) := by
  have hq1 : -1 < (q+1).re := by change -1 < q.re+1; linarith
  obtain ⟨A,hA,hb⟩ := regularizedSlowSolution_allOrders_remainder j (q+1) 6 hq1
  let c : ℂ := -2*m*q*(5-q)
  refine ⟨‖c‖*A*4^(j+2),by positivity,?_⟩
  intro t ht
  let x := radialFreeSlowArgument t
  have hx : x ≠ 0 := radialFreeSlowArgument_ne_zero t
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hv : radialFreeSlowVelocity q m t=c/x*normalizedSlowSolution (q+1) 6 x := by
    rw [radialFreeSlowVelocity,normalizedSlowFirst_eq_shift q 6 _ hq
      (by rw [radialFreeSlowArgument_re]) hx]
    dsimp only [c,x]
    norm_num only [Nat.cast_ofNat]
    field_simp
  have hrec : 4*Complex.I*(Real.exp (-2*t) : ℂ)=1/x :=
    (eq_div_iff hx).mpr (radialFreeSlowArgument_reciprocal t)
  have hp : radialExteriorPolynomialFunction (radialPolynomialEuler
      (radialFreeExpansion (-2*q) m (j+1))) t =
      c/x*slowAsymptoticPolynomial (q+1) 6 j x := by
    rw [radialExteriorPolynomialFunction,radialFreeExpansion_euler_eval_slowAsymptotic
      q m x _ j (radialFreeSlowArgument_reciprocal t)]
    calc
      _ = c*(4*Complex.I*(Real.exp (-2*t) : ℂ))*slowAsymptoticPolynomial (q+1) 6 j x := by
        dsimp [c]; ring
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

end DefocusingNLS

end OAI
