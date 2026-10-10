import OAI.NumberTheory.Ostmann.ZeroDensity.DensityNormalizedEquation

namespace OAI

/-! # Conjugating the actual smoothed square -/

namespace Ostmann

open Complex MeasureTheory
open scoped ComplexConjugate

 theorem density_nat_cpow_conj (q : ℕ) (s : ℂ) :
    (q : ℂ) ^ conj s = conj ((q : ℂ) ^ s) := by
  have ha : (q : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg q)]
    exact Real.pi_pos.ne
  simpa only [map_natCast] using Complex.cpow_conj (q : ℂ) s ha

 theorem densityCompletedSquare_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densityCompletedSquare χ.inverse (conj s) = conj (densityCompletedSquare χ s) := by
  simp only [densityCompletedSquare, PrimitiveComplexCharacter.inverse_modulus,
    χ.inverse_completed_eq_conjugate, Function.comp_apply, Complex.conj_conj,
    density_nat_cpow_conj, map_mul, map_pow]

 theorem densitySquareNormalizer_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densitySquareNormalizer χ.inverse (conj s) = conj (densitySquareNormalizer χ s) := by
  unfold densitySquareNormalizer
  rw [χ.gammaFactor_inverse_conj, PrimitiveComplexCharacter.inverse_modulus,
    density_nat_cpow_conj, map_mul, map_pow]

 theorem densitySquareContour_inverse_conj (χ : PrimitiveComplexCharacter) (s w : ℂ) :
    densitySquareContour χ.inverse (conj s) (conj w) = conj (densitySquareContour χ s w) := by
  unfold densitySquareContour densitySquareGaussian
  rw [← map_add, densityCompletedSquare_inverse_conj]
  simp only [map_div₀, map_mul]
  rw [← map_pow, Complex.exp_conj]

 theorem densitySquareIntegral_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densitySquareIntegral χ.inverse (conj s) = conj (densitySquareIntegral χ s) := by
  have he (u : ℝ) : densitySquareContour χ.inverse (conj s) (1 + u * I) =
      conj (densitySquareContour χ s (1 + (-u : ℝ) * I)) := by
    simpa only [map_add, map_one, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg, neg_mul, mul_neg, neg_neg] using
      densitySquareContour_inverse_conj χ s (1 + (-u : ℝ) * I)
  unfold densitySquareIntegral
  simp_rw [he]
  rw [integral_conj]
  have hn := integral_neg_eq_self (fun u : ℝ => densitySquareContour χ s (1 + u * I)) volume
  rw [hn]
  simp only [map_mul, map_inv₀, map_ofNat, Complex.conj_ofReal]

 theorem densitySmoothedSquare_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densitySmoothedSquare χ.inverse (conj s) = conj (densitySmoothedSquare χ s) := by
  unfold densitySmoothedSquare
  rw [densitySquareIntegral_inverse_conj, densitySquareNormalizer_inverse_conj, map_div₀]

 theorem density_L_fourth_single_bound (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    ‖χ.L s‖ ^ 4 ≤ 4 * ‖densitySmoothedSquare χ s‖ ^ 2 := by
  have h := density_L_fourth_bound χ s hs
  rw [density_critical_reflection s hs, densitySmoothedSquare_inverse_conj, norm_conj] at h
  linarith

end Ostmann

end OAI
