import OAI.Analysis.HyperbolicCones.DeformationBasic

namespace OAI

noncomputable section

open Polynomial Set

namespace Paper256

theorem intervalPolynomial_expanded (a b : ℝ) :
    intervalPolynomial a b = 1 + C (b⁻¹ - a⁻¹) * X + C (-(a⁻¹ * b⁻¹)) * X ^ 2 := by
  simp [intervalPolynomial, map_sub, map_neg, map_mul]
  ring

theorem quadratic_expansion (p : Polynomial ℝ) (hdegree : p.natDegree ≤ 2)
    (hzero : p.coeff 0 = 1) :
    p = 1 + C (p.coeff 1) * X + C (p.coeff 2) * X ^ 2 := by
  calc
    p = ∑ i ∈ Finset.range 3, C (p.coeff i) * X ^ i :=
      p.as_sum_range_C_mul_X_pow' (by omega)
    _ = _ := by simp [Finset.sum_range_succ, hzero]

theorem normalized_quadratic_representation (p : Polynomial ℝ)
    (hdegree : p.natDegree = 2) (hzero : p.coeff 0 = 1) (hlead : p.coeff 2 < 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ p = intervalPolynomial a b := by
  let c := p.coeff 1
  let d := p.coeff 2
  let r := Real.sqrt (c ^ 2 - 4 * d)
  have hd : d < 0 := hlead
  have hdisc : 0 < c ^ 2 - 4 * d := by nlinarith [sq_nonneg c]
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = c ^ 2 - 4 * d := Real.sq_sqrt hdisc.le
  have hminus : 0 < r - c := by nlinarith
  have hplus : 0 < r + c := by nlinarith
  let a := 2 / (r - c)
  let b := 2 / (r + c)
  have ha : 0 < a := div_pos (by norm_num) hminus
  have hb : 0 < b := div_pos (by norm_num) hplus
  have hc : b⁻¹ - a⁻¹ = c := by dsimp [a, b]; rw [inv_div, inv_div]; ring
  have hd' : -(a⁻¹ * b⁻¹) = d := by
    dsimp [a, b]
    rw [inv_div, inv_div]
    nlinarith [hr2]
  refine ⟨a, b, ha, hb, ?_⟩
  rw [intervalPolynomial_expanded, hc, hd']
  exact quadratic_expansion p hdegree.le hzero

theorem intervalPolynomial_natDegree_le (a b : ℝ) :
    (intervalPolynomial a b).natDegree ≤ 2 := by
  rw [intervalPolynomial_expanded]
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · simp
    · simpa using (natDegree_C_mul_X_pow_le (b⁻¹ - a⁻¹) 1).trans (by norm_num : 1 ≤ 2)
  · exact natDegree_C_mul_X_pow_le _ _

theorem intervalPolynomial_coeff_two (a b : ℝ) :
    (intervalPolynomial a b).coeff 2 = -(a⁻¹ * b⁻¹) := by
  rw [intervalPolynomial_expanded]
  simp only [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_one]
  norm_num

theorem intervalPolynomial_natDegree (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (intervalPolynomial a b).natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (intervalPolynomial_natDegree_le a b)
  rw [intervalPolynomial_coeff_two]
  exact neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero ha.ne') (inv_ne_zero hb.ne'))

theorem deformedPolynomial_natDegree (a b η t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    (deformedPolynomial a b η t).natDegree = 2 := by
  rw [deformedPolynomial_scaled]
  exact intervalPolynomial_natDegree _ _ (div_pos ha (timeScale_positive η t hη))
    (div_pos hb (timeScale_positive η t hη))

/-- In coefficient coordinates on normalized quadratics, negative leading coefficient is open. -/
theorem normalized_negative_quadratics_open :
    IsOpen {v : Fin 2 → ℝ | v 1 < 0} := by
  exact isOpen_lt (continuous_apply 1) continuous_const

/-- Every point of that open coefficient family is exactly one of the displayed quadratics. -/
theorem normalized_negative_quadratics_representation (v : Fin 2 → ℝ) (hv : v 1 < 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      1 + C (v 0) * X + C (v 1) * X ^ 2 = intervalPolynomial a b := by
  apply normalized_quadratic_representation
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_add_le_of_degree_le
      · apply natDegree_add_le_of_degree_le
        · simp
        · simpa using (natDegree_C_mul_X_pow_le (v 0) 1).trans (by norm_num : 1 ≤ 2)
      · exact natDegree_C_mul_X_pow_le _ _
    · norm_num only [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_one]
      simpa using hv.ne
  · simp
  · norm_num only [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_one]
    simpa using hv

end Paper256

end

end OAI
