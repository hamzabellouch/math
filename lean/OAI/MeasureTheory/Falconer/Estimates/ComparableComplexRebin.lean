import OAI.MeasureTheory.Falconer.Estimates.ComparablePositiveRebin
import OAI.MeasureTheory.Falconer.Fourier.GoodSupportedKernelMajorant

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem angular_complex_shell_rebin (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a h n : ℕ) (hA : A.length = a) (hB : B.length = a)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (F : (Fin 4 → Plane) → ℂ) (K : (Fin 4 → Plane) → ℝ≥0∞)
    (T : Set (Fin 4 → Plane)) (hT : MeasurableSet T) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hb : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h, G row col →
      ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict (angularLengthShell (a+n)),
        ‖F x‖ₑ ≤ c*K x)
    (hs : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h, G row col →
      ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict (angularLengthShell (a+n)),
        F x ≠ 0 → x ∈ T) :
    ‖∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        if G row col then
          ∫ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0‖ₑ ≤
    c * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        if angularSeparated Q₁ Q₂ (a+n) row col then
          ∫⁻ x in angularLengthShell (a+n), T.indicator K x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0 := by
  apply (enorm_sum_le _ _).trans
  calc
    _ ≤ ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
          if G row col then c *
            ∫⁻ x in angularLengthShell (a+n), T.indicator K x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
          else 0 := by
      apply Finset.sum_le_sum
      intro row hr
      apply (enorm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro col hcol
      by_cases hg : G row col
      · simp only [hg,↓reduceIte]
        have he := enorm_setIntegral_le_good_kernel (angularFourCellMeasure Q₁ Q₂ ρ ν row col)
          (angularLengthShell (a+n)) T hT F K c hc (hb row hr col hcol hg) (hs row hr col hcol hg)
        rw [lintegral_indicator hT,Measure.restrict_restrict hT,inter_comm]
        exact he
      · simp [hg]
    _ = c * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
          if G row col then
            ∫⁻ x in angularLengthShell (a+n), T.indicator K x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
          else 0 := by simp only [Finset.mul_sum,mul_ite,mul_zero]
    _ ≤ _ := mul_le_mul_right
      (angular_shell_positive_rebin Q₁ Q₂ hQ₁ hQ₂ ρ ν A B a h n hA hB G (T.indicator K)) c

end PlanarFalconer

end OAI
