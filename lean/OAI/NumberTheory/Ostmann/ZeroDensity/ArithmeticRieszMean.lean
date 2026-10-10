import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterCanonicalRieszDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszIntegral

namespace OAI

/-! # Literal finite Riesz sums and character orthogonality -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def rieszTwistMean (g : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X)

noncomputable def rieszResidueMean (q : ℕ) (a : ZMod q) (X : ℝ) : ℂ :=
  rieszTwistMean (fun n => if (n : ZMod q) = a then 1 else 0) X

theorem rieszPrimeTest_norm_le_one (u : ℝ) (hu : 0 ≤ u) : ‖rieszPrimeTest u‖ ≤ 1 := by
  rw [rieszPrimeTest, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) zero_le_one

theorem rieszTwistMean_eq_character (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 0 < X) :
    rieszTwistMean (fun n => χ.character (n : ZMod χ.modulus)) X = characterRieszMean χ X := by
  have hs (n : ℕ) (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) :
      characterMangoldtCoefficient χ n * rieszPrimeTest (n / X) = 0 := by
    by_cases hn0 : n = 0
    · subst n; simp [characterMangoldtCoefficient]
    · have hnlarge : ⌊X⌋₊ < n := by simp only [Finset.mem_Ioc] at hn; omega
      have hlarge : X < n := Nat.lt_of_floor_lt hnlarge
      have hdiv : 1 < (n : ℝ) / X := (one_lt_div hX).mpr hlarge
      simp only [rieszPrimeTest, max_eq_right (by linarith : 1 - (n : ℝ) / X ≤ 0),
        Complex.ofReal_zero, mul_zero]
  rw [characterRieszMean, tsum_eq_sum hs]
  unfold rieszTwistMean
  apply Finset.sum_congr rfl
  intro n _
  unfold characterMangoldtCoefficient
  ring

theorem rieszTwistMean_eq_principal (X : ℝ) (hX : 0 < X) :
    rieszTwistMean (fun _ => 1) X = principalRieszMean X := by
  have hs (n : ℕ) (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) :
      principalMangoldtCoefficient n * rieszPrimeTest (n / X) = 0 := by
    by_cases hn0 : n = 0
    · subst n; simp [principalMangoldtCoefficient]
    · have hnlarge : ⌊X⌋₊ < n := by simp only [Finset.mem_Ioc] at hn; omega
      have hlarge : X < n := Nat.lt_of_floor_lt hnlarge
      have hdiv : 1 < (n : ℝ) / X := (one_lt_div hX).mpr hlarge
      simp only [rieszPrimeTest, max_eq_right (by linarith : 1 - (n : ℝ) / X ≤ 0),
        Complex.ofReal_zero, mul_zero]
  rw [principalRieszMean, tsum_eq_sum hs]
  simp only [rieszTwistMean, principalMangoldtCoefficient, mul_one]

theorem rieszResidueMean_orthogonality (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X : ℝ) :
    (q.totient : ℂ) * rieszResidueMean q a X =
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * rieszTwistMean (fun n => χ (n : ZMod q)) X := by
  classical
  simp only [rieszResidueMean, rieszTwistMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  have ho := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q)
  calc
    _ = (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ (n : ZMod q)) *
        (ArithmeticFunction.vonMangoldt n : ℂ) * rieszPrimeTest (n / X) := by
      rw [ho]
      by_cases hn : (n : ZMod q) = a
      · rw [ite_eq_left hn, ite_eq_left hn.symm]
        ring
      · rw [ite_eq_right hn, ite_eq_right (Ne.symm hn)]
        ring
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      ring

end Ostmann

end OAI
