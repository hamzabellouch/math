import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySquareEquation
import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedCharacterConjugation

namespace OAI

/-! # The normalized square functional equation on the critical line -/

namespace Ostmann

open Complex
open scoped ComplexConjugate

noncomputable def densitySmoothedSquare (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  densitySquareIntegral χ s / densitySquareNormalizer χ s

noncomputable def densitySquareRootFactor (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
    densitySquareNormalizer χ.inverse (1 - s) / densitySquareNormalizer χ s

 theorem density_critical_reflection (s : ℂ) (hs : s.re = 1 / 2) : 1 - s = conj s := by
  apply Complex.ext <;> simp [hs]
  ring

 theorem densitySquareNormalizer_reflected_norm (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    ‖densitySquareNormalizer χ.inverse (1 - s)‖ = ‖densitySquareNormalizer χ s‖ := by
  have hq : (0 : ℝ) < χ.modulus := by exact_mod_cast χ.positive
  rw [density_critical_reflection s hs]
  unfold densitySquareNormalizer
  rw [χ.gammaFactor_inverse_conj]
  simp only [norm_mul, norm_pow, norm_conj, PrimitiveComplexCharacter.inverse_modulus]
  congr 1
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq,
    Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.conj_re]

 theorem densitySquareRootFactor_norm (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : ‖densitySquareRootFactor χ s‖ = 1 := by
  rw [densitySquareRootFactor, norm_div, norm_mul, norm_pow, χ.rootNumber_norm_eq_one,
    one_pow, one_mul, densitySquareNormalizer_reflected_norm χ s hs]
  exact div_self (norm_ne_zero_iff.mpr (densitySquareNormalizer_ne_zero χ s (by linarith)))

 theorem density_L_square_equation (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    χ.L s ^ 2 = densitySmoothedSquare χ s +
      densitySquareRootFactor χ s * densitySmoothedSquare χ.inverse (1 - s) := by
  have hp : 0 < s.re := by linarith
  have hi : 0 < (1 - s).re := by simp; linarith
  have hn := densitySquareNormalizer_ne_zero χ s hp
  have hni := densitySquareNormalizer_ne_zero χ.inverse (1 - s) hi
  have he := congrArg (fun z : ℂ => z / densitySquareNormalizer χ s)
    (densityCompletedSquare_equation χ s hs)
  rw [densityCompletedSquare_div χ s hp] at he
  rw [he]
  unfold densitySmoothedSquare densitySquareRootFactor
  field_simp

 theorem density_L_fourth_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    ‖χ.L s‖ ^ 4 ≤ 2 * ‖densitySmoothedSquare χ s‖ ^ 2 +
      2 * ‖densitySmoothedSquare χ.inverse (1 - s)‖ ^ 2 := by
  have he := norm_add_le (densitySmoothedSquare χ s)
    (densitySquareRootFactor χ s * densitySmoothedSquare χ.inverse (1 - s))
  rw [← density_L_square_equation χ s hs, norm_pow, norm_mul,
    densitySquareRootFactor_norm χ s hs, one_mul] at he
  have hh := pow_le_pow_left₀ (sq_nonneg ‖χ.L s‖) he 2
  nlinarith [sq_nonneg (‖densitySmoothedSquare χ s‖ -
    ‖densitySmoothedSquare χ.inverse (1 - s)‖)]

end Ostmann

end OAI
