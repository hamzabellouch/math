import OAI.NumberTheory.Ostmann.Characters.CharacterFunctionalEquation

namespace OAI

/-! # A sufficient elementary bound for the character root number -/

namespace Ostmann

open Complex
open scoped BigOperators Classical

/-- The triangle inequality is sufficient for the growth estimate; no sharp
Gauss-sum evaluation is required here. -/
theorem PrimitiveComplexCharacter.rootNumber_norm_le (χ : PrimitiveComplexCharacter) :
    ‖@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character‖ ≤ χ.modulus := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hG : ‖gaussSum χ.character ZMod.stdAddChar‖ ≤ (χ.modulus : ℝ) := by
    unfold gaussSum
    calc
      _ ≤ ∑ x : ZMod χ.modulus, ‖χ.character x * ZMod.stdAddChar x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : ZMod χ.modulus, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        have hnorm : ‖ZMod.stdAddChar x‖ = 1 := by simp [ZMod.stdAddChar_apply]
        rw [norm_mul, hnorm, mul_one]
        exact χ.character.norm_le_one x
      _ = _ := by simp
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hp : 1 ≤ ‖(χ.modulus : ℂ) ^ (1 / 2 : ℂ)‖ := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.one_le_rpow hq
    norm_num
  simp only [DirichletCharacter.rootNumber, norm_div, norm_pow, norm_I, one_pow, div_one]
  apply (div_le_iff₀ (by linarith : 0 < ‖(χ.modulus : ℂ) ^ (1 / 2 : ℂ)‖)).mpr
  nlinarith

end Ostmann

end OAI
