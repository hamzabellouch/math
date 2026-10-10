import OAI.NumberTheory.Ostmann.Quadratic.QuadraticInverseBudget

namespace OAI

/-! # Concrete denominator and error ranges for the inverse step -/

namespace Ostmann

theorem quadratic_inverse_ranges (T K B J Y R c : ℝ)
    (hT : 1 ≤ T) (hK : 0 ≤ K) (hB : 3 ≤ B) (hJ : 1 ≤ J)
    (hY : Real.exp (4 * T) ≤ Y) (hR : 0 < R) (hc : 0 < c)
    (hcupper : c ≤ Real.exp (3 * T / 25)) (hscale : Y ^ 2 = R / c)
    (hfactor : 1024 * J ^ 4 * (1 + 2 * Real.log ((B + 1) * Y)) * Real.exp (4 * K) ≤
      Real.exp (T / 100)) :
    let δ := Real.exp (-K) / J
    (512 * (1 + 2 * Real.log ((B + 1) * Y)) ≤ δ ^ 3 * Y) ∧
    (1024 * c / δ ^ 2 ≤ Real.exp (13 * T / 100)) ∧
    (1024 * (1 + 2 * Real.log ((B + 1) * Y)) / (δ ^ 4 * Y ^ 2) ≤
      Real.exp (13 * T / 100) / R) := by
  let E := J * Real.exp K
  let L := 1 + 2 * Real.log ((B + 1) * Y)
  have hE : 1 ≤ E := by
    dsimp [E]
    have he : 1 ≤ Real.exp K := Real.one_le_exp_iff.mpr hK
    nlinarith
  have hEpos : 0 < E := by linarith
  have hY1 : 1 ≤ Y := (Real.one_le_exp_iff.mpr (by linarith)).trans hY
  have hYpos : 0 < Y := by linarith
  have hL : 1 ≤ L := by
    have hh : 0 ≤ Real.log ((B + 1) * Y) := Real.log_nonneg (by nlinarith)
    dsimp [L]
    linarith
  have hδ : Real.exp (-K) / J = E⁻¹ := by
    dsimp [E]
    rw [Real.exp_neg, mul_inv_rev]
    ring
  have hf : 1024 * E ^ 4 * L ≤ Real.exp (T / 100) := by
    simpa only [E, L, mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat,
      mul_assoc, mul_left_comm, mul_comm] using hfactor
  have h23 : E ^ 2 ≤ E ^ 4 := pow_le_pow_right₀ hE (by omega)
  have h34 : E ^ 3 ≤ E ^ 4 := pow_le_pow_right₀ hE (by omega)
  have hsecond : 1024 * E ^ 2 ≤ Real.exp (T / 100) := by
    apply le_trans _ hf
    nlinarith [mul_le_mul_of_nonneg_left h23 (by norm_num : (0 : ℝ) ≤ 1024),
      mul_le_mul_of_nonneg_left hL (show 0 ≤ 1024 * E ^ 4 by positivity)]
  have hthird : 512 * L * E ^ 3 ≤ Real.exp (T / 100) := by
    apply le_trans _ hf
    have hh := mul_le_mul_of_nonneg_left h34 (show 0 ≤ 512 * L by positivity)
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ E ^ 4 by positivity)]
  have hcprod : c * Real.exp (T / 100) ≤ Real.exp (13 * T / 100) := by
    calc
      _ ≤ Real.exp (3 * T / 25) * Real.exp (T / 100) :=
        mul_le_mul_of_nonneg_right hcupper (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  dsimp only
  rw [hδ]
  refine ⟨?_, ?_, ?_⟩
  · change 512 * L ≤ E⁻¹ ^ 3 * Y
    rw [inv_pow, mul_comm (E ^ 3)⁻¹ Y, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hEpos _)).mpr
    exact hthird.trans ((Real.exp_le_exp.mpr (by linarith)).trans hY)
  · rw [inv_pow, div_inv_eq_mul]
    calc
      1024 * c * E ^ 2 = c * (1024 * E ^ 2) := by ring
      _ ≤ c * Real.exp (T / 100) := mul_le_mul_of_nonneg_left hsecond hc.le
      _ ≤ _ := hcprod
  · have heq : 1024 * L / (E⁻¹ ^ 4 * Y ^ 2) = (1024 * E ^ 4 * L) * c / R := by
      rw [hscale]
      field_simp
    change 1024 * L / (E⁻¹ ^ 4 * Y ^ 2) ≤ _
    rw [heq]
    apply div_le_div_of_nonneg_right _ hR.le
    calc
      _ ≤ Real.exp (T / 100) * c := mul_le_mul_of_nonneg_right hf hc.le
      _ ≤ _ := by simpa only [mul_comm] using hcprod

end Ostmann

end OAI
