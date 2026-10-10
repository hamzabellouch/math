import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorDichotomy
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityAbscissaPolynomial

namespace OAI

/-! # The original polynomial alternative as one common coefficient sequence -/

namespace Ostmann

open Complex
open scoped BigOperators Classical

 theorem densityDetectorWeight_norm_le_one (x : ℝ) (hx : 0 ≤ x) : ‖densityDetectorWeight x‖ ≤ 1 := by
  by_cases h1 : 1 ≤ x
  · rw [densityDetectorWeight_zero x h1, norm_zero]
    norm_num
  · have hle : x ≤ 1 := le_of_not_ge h1
    rw [densityDetectorWeight_eq x hle, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1 - x) ^ 2 / 2)]
    nlinarith

noncomputable def densityPolynomialCoefficient (X : ℕ) (Y : ℝ) (n : ℕ) : ℂ :=
  if X < n then densityDetectorCoefficient X n * densityDetectorWeight (n / Y) else 0

 theorem densityPolynomialCoefficient_norm (X : ℕ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) :
    ‖densityPolynomialCoefficient X Y n‖ ≤ n.divisors.card := by
  unfold densityPolynomialCoefficient
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul (densityDetectorCoefficient_norm X n)
      (densityDetectorWeight_norm_le_one (n / Y) (by positivity)) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  · simp

 theorem densityPolynomialCoefficient_below (X n : ℕ) (Y : ℝ) (hn : n ≤ X) :
    densityPolynomialCoefficient X Y n = 0 := by
  simp [densityPolynomialCoefficient, Nat.not_lt.mpr hn]

 theorem densityPolynomialCoefficient_above (X n : ℕ) (Y : ℝ) (hY : 0 < Y) (hn : Y ≤ n) :
    densityPolynomialCoefficient X Y n = 0 := by
  simp [densityPolynomialCoefficient, densityDetectorWeight_zero (n / Y)
    ((le_div_iff₀ hY).mpr (by simpa using hn))]

 theorem densityDetector_polynomial (χ : PrimitiveComplexCharacter) (X : ℕ) (Y β t : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
      LSeries.term (densityDetectorCharacterCoefficient χ X) (densityVerticalPoint β t) n *
        densityDetectorWeight (n / Y)) =
      densityCharacterPolynomial (Finset.Icc 1 ⌊Y⌋₊)
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) β) χ.character t := by
  rw [Finset.sum_filter]
  unfold densityCharacterPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : 0 < n := (Finset.mem_Icc.mp hn).1
  by_cases hX : X < n
  · rw [ite_eq_left hX, LSeries.term_of_ne_zero hnp.ne', densityDetectorCharacterCoefficient,
      density_vertical_term _ β t n hnp]
    unfold densityVerticalCoeff densityPolynomialCoefficient
    rw [ite_eq_left hX]
    ring
  · simp [hX, densityVerticalCoeff, densityPolynomialCoefficient]

end Ostmann

end OAI
