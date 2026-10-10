import OAI.NumberTheory.Ostmann.Characters.CharacterMellinIntegral

namespace OAI

/-! # A quantitative bound in the positive half-plane

The bounded periodic prefix sums give the polynomial growth needed for
local Jensen estimates, without assuming a convexity estimate for L.
-/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

theorem PrimitiveComplexCharacter.L_integral_positive (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) :
    χ.L s = s * ∫ t in Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) *
        (t : ℂ) ^ (-(s + 1)) := by
  rw [← characterMellinL_eq_L χ s hs, characterMellinL, characterSummatory_mellin]

theorem PrimitiveComplexCharacter.L_norm_bound_positive (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) :
    ‖χ.L s‖ ≤ ‖s‖ * ((χ.modulus : ℝ) + 1) / s.re := by
  have hg : IntegrableOn (fun t : ℝ => ((χ.modulus : ℝ) + 1) * t ^ (-s.re - 1))
      (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hmean : ‖∫ t in Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) *
        (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Ioi (1 : ℝ), ((χ.modulus : ℝ) + 1) * t ^ (-s.re - 1) := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    have ht0 : 0 < t := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    rw [show -(s.re + 1) = -s.re - 1 by ring]
    exact mul_le_mul_of_nonneg_right (χ.prefix_Icc_bound _) (Real.rpow_nonneg ht0.le _)
  have heval : (∫ t in Ioi (1 : ℝ), ((χ.modulus : ℝ) + 1) * t ^ (-s.re - 1)) =
      ((χ.modulus : ℝ) + 1) / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.one_rpow]
    field_simp [hs.ne']
    ring
  rw [χ.L_integral_positive s hs, norm_mul]
  calc
    _ ≤ ‖s‖ * (((χ.modulus : ℝ) + 1) / s.re) :=
      mul_le_mul_of_nonneg_left (hmean.trans_eq heval) (norm_nonneg _)
    _ = _ := by ring

end Ostmann

end OAI
