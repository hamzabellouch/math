import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaShift
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedRightGrowth

namespace OAI

/-! # The entire completed square and its exact reflection -/

namespace Ostmann

open Complex

noncomputable def densityCompletedSquare (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  (χ.modulus : ℂ) ^ s * χ.completed s ^ 2

 theorem densityCompletedSquare_analytic (χ : PrimitiveComplexCharacter) (s : ℂ) :
    AnalyticAt ℂ (densityCompletedSquare χ) s := by
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  exact ((differentiable_id.const_cpow (Or.inl hq)).analyticAt s).mul
    ((χ.completed_analytic s).pow 2)

 theorem densityCompletedSquare_reflection (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densityCompletedSquare χ s =
      (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        densityCompletedSquare χ.inverse (1 - s) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hf := χ.primitive.completedLFunction_one_sub (1 - s)
  rw [show (1 : ℂ) - (1 - s) = s by ring,
    show (1 : ℂ) - s - 1 / 2 = 1 / 2 - s by ring] at hf
  change χ.completed s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
    DirichletCharacter.rootNumber χ.character * χ.inverse.completed (1 - s) at hf
  have hp : (χ.modulus : ℂ) ^ s * ((χ.modulus : ℂ) ^ (1 / 2 - s)) ^ 2 =
      (χ.modulus : ℂ) ^ (1 - s) := by
    rw [← Complex.cpow_mul_nat, ← Complex.cpow_add _ _ hq]
    congr 1
    norm_num
    ring
  unfold densityCompletedSquare
  rw [hf, mul_pow, mul_pow]
  change (χ.modulus : ℂ) ^ s *
    (((χ.modulus : ℂ) ^ (1 / 2 - s)) ^ 2 *
    (DirichletCharacter.rootNumber χ.character) ^ 2 * χ.inverse.completed (1 - s) ^ 2) = _
  calc
    _ = ((χ.modulus : ℂ) ^ s * ((χ.modulus : ℂ) ^ (1 / 2 - s)) ^ 2) *
        (DirichletCharacter.rootNumber χ.character) ^ 2 * χ.inverse.completed (1 - s) ^ 2 := by ring
    _ = _ := by rw [hp, PrimitiveComplexCharacter.inverse_modulus]; ring

 theorem densityCompletedSquare_eq (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 0 < s.re) :
    densityCompletedSquare χ s = (χ.modulus : ℂ) ^ s *
      (DirichletCharacter.gammaFactor χ.character s) ^ 2 * χ.L s ^ 2 := by
  rw [densityCompletedSquare, χ.completed_eq_L_mul_gamma s hs, mul_pow]
  ring

noncomputable def densitySquareNormalizer (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  (χ.modulus : ℂ) ^ s * (DirichletCharacter.gammaFactor χ.character s) ^ 2

 theorem densitySquareNormalizer_ne_zero (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 0 < s.re) : densitySquareNormalizer χ s ≠ 0 := by
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hg : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    intro he
    have hn := χ.gammaInverse_ne_zero s hs
    exact hn (by simp only [PrimitiveComplexCharacter.gammaInverse, he, inv_zero])
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hq)) (pow_ne_zero 2 hg)

 theorem densityCompletedSquare_div (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 0 < s.re) : densityCompletedSquare χ s / densitySquareNormalizer χ s = χ.L s ^ 2 := by
  rw [densityCompletedSquare_eq χ s hs]
  exact mul_div_cancel_left₀ _ (densitySquareNormalizer_ne_zero χ s hs)

end Ostmann

end OAI
