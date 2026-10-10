import OAI.NumberTheory.Ostmann.ZeroDensity.RieszDirichletIntegral
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszUnsmoothing

namespace OAI

/-! # Identifying the Riesz contour with the finite arithmetic sum -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem rieszPrimeTest_scale (X y : ℝ) (hX : 0 < X) :
    rieszPrimeTest (y / X) = ((max (X - y) 0 / X : ℝ) : ℂ) := by
  by_cases hy : y ≤ X
  · have hdiv : y / X ≤ 1 := (div_le_one hX).mpr hy
    rw [rieszPrimeTest, max_eq_left (by linarith : 0 ≤ 1 - y / X),
      max_eq_left (sub_nonneg.mpr hy)]
    push_cast
    field_simp [show (X : ℂ) ≠ 0 by exact_mod_cast hX.ne']
  · have hdiv : 1 < y / X := (one_lt_div hX).mpr (lt_of_not_ge hy)
    rw [rieszPrimeTest, max_eq_right (by linarith : 1 - y / X ≤ 0),
      max_eq_right (by linarith : X - y ≤ 0)]
    simp

theorem characterRieszMean_finite (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 0 < X) :
    (X : ℂ) * characterRieszMean χ X =
      ∑ n ∈ Finset.range (⌊X⌋₊ + 1), characterMangoldtCoefficient χ n *
        (max (X - (n : ℝ)) 0 : ℝ) := by
  have hsupport (n : ℕ) (hn : n ∉ Finset.range (⌊X⌋₊ + 1)) :
      characterMangoldtCoefficient χ n * rieszPrimeTest (n / X) = 0 := by
    have hfloor : ⌊X⌋₊ < n := by simpa using hn
    have hxn : X < n := Nat.lt_of_floor_lt hfloor
    rw [rieszPrimeTest_scale X n hX, max_eq_right (by linarith : X - (n : ℝ) ≤ 0)]
    simp
  rw [characterRieszMean, tsum_eq_sum hsupport, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [rieszPrimeTest_scale X n hX]
  push_cast
  field_simp [show (X : ℂ) ≠ 0 by exact_mod_cast hX.ne']

end Ostmann

end OAI
