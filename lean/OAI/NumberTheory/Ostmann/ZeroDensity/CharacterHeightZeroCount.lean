import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothTruncatedContour

namespace OAI

/-! # A polynomial bound for the finite set of forbidden contour ordinates -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem criticalZerosUpTo_card_bound (χ : PrimitiveComplexCharacter) (T : ℝ) (hT : 0 ≤ T) :
    ((criticalZerosUpTo χ T).card : ℝ) ≤
      (32 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  calc
    _ = ∑ _z ∈ criticalZerosUpTo χ T, (1 : ℝ) := by simp
    _ ≤ ∑ z ∈ criticalZerosUpTo χ T, (characterZeroOrder χ z : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      have he := (mem_criticalZerosUpTo.mp hz).1.2.2
      have ho := (characterZeroOrder_pos_iff χ z).mpr he
      have hi : (1 : ℤ) ≤ characterZeroOrder χ z := ho
      exact_mod_cast hi
    _ ≤ _ := χ.full_zero_sum_rate T hT _ (by
      intro z hz
      obtain ⟨hz, hi⟩ := mem_criticalZerosUpTo.mp hz
      exact ⟨hz.1, hz.2.1, hi⟩)

theorem criticalZerosUpTo_card_polynomial (χ : PrimitiveComplexCharacter) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
      ((criticalZerosUpTo χ (T + 4)).card : ℝ) ≤ C * (T + 5) ^ 2 := by
  let A := 32 / Real.log (14 / 13 : ℝ)
  have hA : 0 < A := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hq : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  refine ⟨2 * A * χ.modulus, by positivity, ?_⟩
  intro T hT
  have hh := criticalZerosUpTo_card_bound χ (T + 4) (by linarith)
  have hl : Real.log ((χ.modulus : ℝ) * (T + 4 + 2)) ≤
      (χ.modulus : ℝ) * (T + 4 + 2) := by
    have he := Real.log_le_sub_one_of_pos
      (by positivity : 0 < (χ.modulus : ℝ) * (T + 4 + 2))
    linarith
  have hx : T + 4 + 2 ≤ 2 * (T + 5) := by linarith
  calc
    _ ≤ A * (T + 4 + 1) * Real.log ((χ.modulus : ℝ) * (T + 4 + 2)) := hh
    _ ≤ A * (T + 4 + 1) * ((χ.modulus : ℝ) * (2 * (T + 5))) := by
      exact mul_le_mul_of_nonneg_left
        (hl.trans (mul_le_mul_of_nonneg_left hx hq.le)) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
