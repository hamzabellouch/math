import OAI.Combinatorics.PolynomialVacuum.Algebra.Target

namespace OAI

namespace PolynomialVacuumAlgebra

theorem q_ne_zero : q ≠ 0 := Complex.exp_ne_zero _

theorem q_pow_four : q^4 = Complex.I := by
  rw [q, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_div_two_mul_I using 1
  push_cast
  ring_nf

theorem q_pow_eight : q^8 = -1 := by
  calc
    q^8 = (q^4)^2 := by ring
    _ = -1 := by rw [q_pow_four,Complex.I_sq]

theorem q_pow_sixteen : q^16 = 1 := by
  calc
    q^16 = (q^8)^2 := by ring
    _ = 1 := by rw [q_pow_eight]; norm_num

theorem q_inv : q⁻¹ = -q^7 := by
  apply (mul_left_cancel₀ q_ne_zero)
  rw [mul_inv_cancel₀ q_ne_zero]
  calc
    1 = -(q^8) := by rw [q_pow_eight]; ring
    _ = q * (-q^7) := by ring

theorem q_four_inv : (q^4)⁻¹ = -q^4 := by
  rw [q_pow_four,Complex.inv_I]

theorem q_five_inv : (q^5)⁻¹ = -q^3 := by
  apply (mul_left_cancel₀ (pow_ne_zero 5 q_ne_zero))
  rw [mul_inv_cancel₀ (pow_ne_zero 5 q_ne_zero)]
  calc
    1 = -(q^8) := by rw [q_pow_eight]; ring
    _ = q^5 * (-q^3) := by ring

theorem q_plus_inv : q + q⁻¹ = (Real.sqrt (2+Real.sqrt 2) : ℝ) := by
  rw [q, ← Complex.exp_neg]
  have ha : Complex.I * (Real.pi / 8 : ℂ) = ((Real.pi/8 : ℝ) : ℂ)*Complex.I := by
    push_cast; ring
  have hb : -(Complex.I * (Real.pi / 8 : ℂ)) = ((-(Real.pi/8) : ℝ) : ℂ)*Complex.I := by
    push_cast; ring
  rw [hb,ha,Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I,
    Real.cos_neg,Real.sin_neg,Real.cos_pi_div_eight]
  push_cast
  ring

theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
theorem sqrt_two_sq : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
theorem sqrt_two_ne_one : Real.sqrt 2 ≠ (1 : ℝ) := by
  intro he
  nlinarith [sqrt_two_sq]

theorem xStar_mul_q_sum : xStar*(q+q⁻¹) = 1 := by
  rw [q_plus_inv,xStar,← Complex.ofReal_mul]
  rw [inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity : (0:ℝ)<2+Real.sqrt 2)))]
  rfl

theorem q_two_sum : q^2-q^6 = (Real.sqrt 2 : ℝ) := by
  have h := congrArg (fun z : ℂ => z^2) q_plus_inv
  have hs : ((Real.sqrt (2+Real.sqrt 2) : ℝ) : ℂ)^2 = 2+(Real.sqrt 2 : ℝ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2+Real.sqrt 2)
  rw [hs] at h
  have hqi : q*q⁻¹=1 := mul_inv_cancel₀ q_ne_zero
  have hinv : (q⁻¹)^2 = -q^6 := by
    rw [q_inv]
    calc
      (-q^7)^2 = q^6*q^8 := by ring
      _ = -q^6 := by rw [q_pow_eight]; ring
  calc
    q^2-q^6 = (q+q⁻¹)^2-2 := by rw [add_sq,hinv]; linear_combination -2*hqi
    _ = ((Real.sqrt 2 : ℝ) : ℂ) := by rw [h]; ring

theorem xStar_sq_mul_sqrt_two : xStar^2*(Real.sqrt 2 : ℝ)=nZero := by
  have hs : (Real.sqrt (2+Real.sqrt 2))^2=2+Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hr : Real.sqrt (2+Real.sqrt 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hc : ((Real.sqrt (2+Real.sqrt 2))⁻¹)^2*Real.sqrt 2=Real.sqrt 2-1 := by
    field_simp
    nlinarith [sqrt_two_sq]
  dsimp only [xStar,nZero]
  exact_mod_cast hc

theorem xStar_sq_twice : 1-2*xStar^2=nZero := by
  have hs : (Real.sqrt (2+Real.sqrt 2))^2=2+Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hr : Real.sqrt (2+Real.sqrt 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hc : 1-2*((Real.sqrt (2+Real.sqrt 2))⁻¹)^2=Real.sqrt 2-1 := by
    field_simp
    nlinarith [sqrt_two_sq]
  dsimp only [xStar,nZero]
  exact_mod_cast hc

theorem nZero_ne_zero : nZero ≠ 0 := by
  change ((Real.sqrt 2 : ℝ) : ℂ) - 1 ≠ 0
  exact_mod_cast sub_ne_zero.mpr sqrt_two_ne_one

theorem t_ne_zero : t ≠ 0 := pow_ne_zero _ q_ne_zero
theorem T_ne_zero : T ≠ 0 := pow_ne_zero _ t_ne_zero

end PolynomialVacuumAlgebra

end OAI
