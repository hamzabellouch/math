import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMollifierProduct
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorAnalytic

namespace OAI

/-! # Elementary growth bounds for the actual zero-detector product -/

namespace Ostmann

open Complex
open scoped BigOperators

 theorem densityMollifier_norm_le (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 0 ≤ s.re) : ‖densityMollifier X χ.character s‖ ≤ X := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnp
      have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        norm_cast
        exact ArithmeticFunction.abs_moebius_le_one
      rw [norm_div, norm_mul, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      apply (div_le_div_of_nonneg_right
        (mul_le_mul (χ.character.norm_le_one _) hμ (norm_nonneg _) zero_le_one)
        (Real.rpow_nonneg (by positivity) s.re)).trans
      rw [one_mul]
      exact (div_le_one (Real.rpow_pos_of_pos (by positivity) s.re)).mpr
        (Real.one_le_rpow hnR hs)
    _ = _ := by simp [Nat.card_Icc]

 theorem density_L_short_positive_bound (χ : PrimitiveComplexCharacter) (z : ℂ)
    (hz : 1 / 2 ≤ z.re) (hz3 : z.re ≤ 3) :
    ‖χ.L z‖ ≤ 2 * ((χ.modulus : ℝ) + 1) * (3 + |z.im|) := by
  have hzp : 0 < z.re := by linarith
  have hn : ‖z‖ ≤ 3 + |z.im| := by
    apply (Complex.norm_le_abs_re_add_abs_im z).trans
    rw [abs_of_pos hzp]
    linarith
  apply (χ.L_norm_bound_positive z hzp).trans
  apply (div_le_iff₀ hzp).mpr
  have h1 := mul_le_mul_of_nonneg_right hn (show 0 ≤ (χ.modulus : ℝ) + 1 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hz
    (show 0 ≤ 2 * ((χ.modulus : ℝ) + 1) * (3 + |z.im|) by positivity)
  nlinarith

 theorem densityDetector_numerator_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (_hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (Y : ℝ) (hY : 1 ≤ Y)
    (x u : ℝ) (hx : 1 / 2 - s.re ≤ x) (hx2 : x ≤ 2) :
    ‖χ.L (s + ((x : ℂ) + u * I)) * densityMollifier X χ.character (s + ((x : ℂ) + u * I)) *
      (Y : ℂ) ^ ((x : ℂ) + u * I)‖ ≤
        (2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 * (3 + |s.im|)) * (1 + |u|) := by
  have hz : 1 / 2 ≤ (s + ((x : ℂ) + u * I)).re := by simp; linarith
  have hz3 : (s + ((x : ℂ) + u * I)).re ≤ 3 := by simp; linarith
  have hL := density_L_short_positive_bound χ _ hz hz3
  have hM := densityMollifier_norm_le χ X _ (by linarith)
  have hpow : ‖(Y : ℂ) ^ ((x : ℂ) + u * I)‖ ≤ Y ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Y)]
    have he : (((x : ℂ) + u * I).re) = x := by simp
    rw [he, ← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hY hx2
  have him : |(s + ((x : ℂ) + u * I)).im| ≤ |s.im| + |u| := by
    simpa using abs_add_le s.im u
  rw [norm_mul, norm_mul]
  apply (mul_le_mul (mul_le_mul hL hM (norm_nonneg _) (by positivity)) hpow
    (norm_nonneg _) (by positivity)).trans
  have hsimple : 3 + |(s + ((x : ℂ) + u * I)).im| ≤ (3 + |s.im|) * (1 + |u|) := by
    nlinarith [abs_nonneg s.im, abs_nonneg u]
  have h := mul_le_mul_of_nonneg_left hsimple
    (show 0 ≤ 2 * ((χ.modulus : ℝ) + 1) * X * Y ^ 2 by positivity)
  convert h using 1 <;> ring

end Ostmann

end OAI
