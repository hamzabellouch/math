import OAI.NumberTheory.Ostmann.ZeroDensity.RieszExponentialParameters

namespace OAI

/-! # Exponential decay for the actual nonexceptional Riesz means -/

namespace Ostmann

open Filter

theorem riesz_height_log_bound (y : ℝ) (hy : 5 ≤ y) (Q : ℕ)
    (hQ : 1 ≤ Q) (hQy : (Q : ℝ) ≤ Real.exp y) :
    0 < Real.log (2 * (Q : ℝ) * (Real.exp y + 2)) ∧
      Real.log (2 * (Q : ℝ) * (Real.exp y + 2)) ≤ 3 * y := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hT : 2 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hpos : 1 < 2 * (Q : ℝ) * (Real.exp y + 2) := by nlinarith
  refine ⟨Real.log_pos hpos, ?_⟩
  have hprod : 2 * (Q : ℝ) * (Real.exp y + 2) ≤ 4 * (Real.exp y) ^ 2 := by
    nlinarith [Real.exp_pos y]
  calc
    _ ≤ Real.log (4 * (Real.exp y) ^ 2) := Real.log_le_log (by linarith) hprod
    _ = Real.log 4 + 2 * y := by rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_exp]; norm_num
    _ ≤ 3 * y := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]

theorem nonexceptional_character_riesz_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ y : ℝ in atTop, ∀ Q : ℕ, 101 ≤ Q → (Q : ℝ) ≤ Real.exp y →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q → some χ ≠ exception →
        ‖characterRieszMean χ (Real.exp (y ^ 2))‖ ≤
          3 * Real.exp (y ^ 2 - d * y) := by
  obtain ⟨c, A, B, E, hc, hc4, hA, hB, hE, hbound⟩ := nonexceptional_character_riesz_bound
  refine ⟨c / 6, by positivity, ?_⟩
  filter_upwards [riesz_exponential_error c A B E hc hc4 hA.le hB.le hE.le,
    eventually_ge_atTop (5 : ℝ)] with y hy hy5
  intro Q hQ hQy
  have hy0 : 0 < y := by linarith
  have hT : 2 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  obtain ⟨exception, he⟩ := hbound Q hQ (Real.exp y) hT
  refine ⟨exception, ?_⟩
  intro χ hχ hne
  have hb1 : 1 < 1 + 1 / y ^ 2 := by
    have hh : 0 < 1 / y ^ 2 := by positivity
    linarith
  have hb2 : 1 + 1 / y ^ 2 ≤ 2 := by
    have hys : 1 ≤ y ^ 2 := by nlinarith
    have hh : 1 / y ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hys
    linarith
  have hr := he χ hχ hne (Real.exp (y ^ 2)) (1 + 1 / y ^ 2)
    (Real.one_le_exp (sq_nonneg y)) hb1 hb2
  obtain ⟨hH, hHy⟩ := riesz_height_log_bound y hy5 Q (by omega) hQy
  exact hr.trans (hy _ hH hHy)

theorem nonexceptional_character_riesz_sqrt_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ Q : ℕ, 101 ≤ Q →
      (Q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q → some χ ≠ exception →
        ‖characterRieszMean χ X‖ ≤
          3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, h⟩ := nonexceptional_character_riesz_decay
  refine ⟨d, hd, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hx : 0 < X := by linarith
  have heq : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx]
  intro Q hQ hQX
  obtain ⟨exception, he⟩ := hX Q hQ hQX
  refine ⟨exception, ?_⟩
  intro χ hχ hne
  have hh := he χ hχ hne
  dsimp only [Function.comp_apply] at hh
  rw [heq, Real.exp_sub, Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx,
    div_eq_mul_inv, ← Real.exp_neg] at hh
  simpa only [mul_assoc, neg_mul] using hh

end Ostmann

end OAI
