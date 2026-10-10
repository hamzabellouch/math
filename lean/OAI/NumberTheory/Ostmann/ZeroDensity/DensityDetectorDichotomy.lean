import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorShift

namespace OAI

/-! # The actual polynomial-or-critical-integral alternative at every zero -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem densityDetector_dichotomy (χ : PrimitiveComplexCharacter) (X : ℕ) (hX : 1 ≤ X)
    (s : ℂ) (hs : 1 / 2 < s.re) (hs1 : s.re ≤ 1) (hz : χ.L s = 0)
    (Y : ℝ) (hY : 4 ≤ Y) :
    (1 / 8 : ℝ) ≤ ‖∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
      LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y)‖ ∨
    (1 / 8 : ℝ) ≤ ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
      densityDetectorIntegrand χ X s Y (((1 / 2 - s.re : ℝ) : ℂ) + u * I)‖ := by
  let P : ℂ := ∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
    LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y)
  by_cases hp : (1 / 8 : ℝ) ≤ ‖P‖
  · exact Or.inl hp
  · right
    have hsplit := densityDetectorMean_split χ X hX s Y (by linarith)
    have he : densityDetectorWeight (1 / Y) = densityDetectorMean χ X s Y - P := by
      rw [hsplit]
      dsimp [P]
      ring
    have hn := norm_sub_le (densityDetectorMean χ X s Y) P
    rw [← he] at hn
    have hw : (1 / 4 : ℝ) ≤ ‖densityDetectorWeight (1 / Y)‖ :=
      (densityDetectorWeight_at_one_div Y hY).trans (Complex.re_le_norm _)
    have hm : (1 / 8 : ℝ) ≤ ‖densityDetectorMean χ X s Y‖ := by
      have hp' : ‖P‖ < 1 / 8 := lt_of_not_ge hp
      linarith
    rwa [densityDetectorMean_at_zero χ X s hs hs1 hz Y (by linarith)] at hm

end Ostmann

end OAI
