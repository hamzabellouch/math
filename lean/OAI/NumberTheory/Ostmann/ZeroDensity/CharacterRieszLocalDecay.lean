import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterRieszLocalBound
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszExponentialParameters

namespace OAI

/-! # Exponential decay with the actual local exceptional-zero contribution -/

namespace Ostmann

open Filter

theorem character_riesz_height_log_bound (χ : PrimitiveComplexCharacter) (y : ℝ)
    (hy : 5 ≤ y) (hχ : (χ.modulus : ℝ) ≤ Real.exp y) :
    0 < Real.log χ.modulus + Real.log (Real.exp y + 4) + 1 ∧
      Real.log χ.modulus + Real.log (Real.exp y + 4) + 1 ≤ 3 * y := by
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (Real.exp y + 4) := Real.log_nonneg (by linarith [Real.exp_pos y])
  refine ⟨by linarith, ?_⟩
  have hqy : Real.log χ.modulus ≤ y := by
    simpa only [Real.log_exp] using Real.log_le_log (by exact_mod_cast χ.positive) hχ
  have he : 4 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hty : Real.log (Real.exp y + 4) ≤ Real.log 2 + y := by
    calc
      _ ≤ Real.log (2 * Real.exp y) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem character_riesz_local_decay : ∃ c d : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ c ≤ actualPageConstant / 10 ∧ 0 < d ∧
    ∀ᶠ y : ℝ in atTop, ∀ χ : PrimitiveComplexCharacter, (χ.modulus : ℝ) ≤ Real.exp y →
      let H := Real.log χ.modulus + Real.log (Real.exp y + 4) + 1
      ∃ e : Option ℕ,
        (∀ i, e = some i → 1 - 2 * c / H < ((actualCharacterZeros χ).zeros i).re ∧
          χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0) ∧
        (∀ i, 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
          |((actualCharacterZeros χ).zeros i).im| ≤ Real.exp y → e = some i) ∧
        ‖characterRieszMean χ (Real.exp (y ^ 2)) -
            characterRieszZeroTerm χ (Real.exp (y ^ 2)) e‖ ≤
          3 * Real.exp (y ^ 2 - d * y) := by
  obtain ⟨c, A, B, E, hc, hc4, hcp, hA, hB, hE, hbound⟩ := character_riesz_local_bound
  refine ⟨c, c / 6, hc, hc4, hcp, by positivity, ?_⟩
  filter_upwards [riesz_exponential_error c A B E hc hc4 hA.le hB.le hE.le,
    eventually_ge_atTop (5 : ℝ)] with y hy hy5
  intro χ hχ
  have hy0 : 0 < y := by linarith
  have hT : 2 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  obtain ⟨e, he, hec, hb⟩ := hbound χ (Real.exp y) hT
  refine ⟨e, he, hec, ?_⟩
  have hb1 : 1 < 1 + 1 / y ^ 2 := by
    have hh : 0 < 1 / y ^ 2 := by positivity
    linarith
  have hb2 : 1 + 1 / y ^ 2 ≤ 2 := by
    have hys : 1 ≤ y ^ 2 := by nlinarith
    have hh : 1 / y ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hys
    linarith
  have hr := hb (Real.exp (y ^ 2)) (1 + 1 / y ^ 2)
    (Real.one_le_exp (sq_nonneg y)) hb1 hb2
  obtain ⟨hH, hHy⟩ := character_riesz_height_log_bound χ y hy5 hχ
  exact hr.trans (hy _ hH hHy)

theorem character_riesz_local_sqrt_decay : ∃ c d : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ c ≤ actualPageConstant / 10 ∧ 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ χ : PrimitiveComplexCharacter,
      (χ.modulus : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      let T := Real.exp (Real.sqrt (Real.log X))
      let H := Real.log χ.modulus + Real.log (T + 4) + 1
      ∃ e : Option ℕ,
        (∀ i, e = some i → 1 - 2 * c / H < ((actualCharacterZeros χ).zeros i).re ∧
          χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0) ∧
        (∀ i, 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
          |((actualCharacterZeros χ).zeros i).im| ≤ T → e = some i) ∧
        ‖characterRieszMean χ X - characterRieszZeroTerm χ X e‖ ≤
          3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨c, d, hc, hc4, hcp, hd, h⟩ := character_riesz_local_decay
  refine ⟨c, d, hc, hc4, hcp, hd, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hx : 0 < X := by linarith
  have heq : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx]
  intro χ hχ
  obtain ⟨e, he, hec, hb⟩ := hX χ hχ
  refine ⟨e, he, hec, ?_⟩
  dsimp only [Function.comp_apply] at hb
  rw [heq, Real.exp_sub, Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx] at hb
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, neg_mul] using hb

end Ostmann

end OAI
