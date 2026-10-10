import OAI.MeasureTheory.Falconer.Measures.ComparableIntegralPartition
import OAI.MeasureTheory.Falconer.Estimates.ActualComparableFarError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem angular_comparable_contribution_partition (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a d : ℕ) (hA : A.length = a) (hB : B.length = a)
    (v Ma₁ Ma₂ : ℝ) (F : (Fin 4 → Plane) → ℂ)
    (hF : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
      ¬ angularNear Q₁ Q₂ (a+d) row col →
      IntegrableOn F angularLengthComparable (angularFourCellMeasure Q₁ Q₂ ρ ν row col)) :
    angularComparableFarContribution Q₁ Q₂ ρ ν A B a d v Ma₁ Ma₂ F =
      ∑ b ∈ Finset.Icc (a+9) (a+d+5),
        (((2:ℝ)^(2*(v-a)))/(Ma₁^2*Ma₂^2)) •
          ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
            ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
              if ¬ angularNear Q₁ Q₂ (a+d) row col then
                ∫ x in angularLengthShell b, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
              else 0 := by
  unfold angularComparableFarContribution
  rw [← Finset.smul_sum]
  congr 1
  calc
    _ = ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
          ∑ b ∈ Finset.Icc (a+9) (a+d+5),
            if ¬ angularNear Q₁ Q₂ (a+d) row col then
              ∫ x in angularLengthShell b, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
            else 0 := by
      apply Finset.sum_congr rfl
      intro row hr
      apply Finset.sum_congr rfl
      intro col hc
      by_cases hf : ¬ angularNear Q₁ Q₂ (a+d) row col
      · simp only [ite_eq_left hf]
        exact angular_comparable_integral_partition Q₁ Q₂ hQ₁ hQ₂ ρ ν A B a d hA hB row col hr hc hf F
          (hF row hr col hc hf)
      · simp [hf]
    _ = _ := by
      simp_rw [Finset.sum_comm (s := sourceProductVertices Q₁ Q₂ ρ ν A B d)
        (t := Finset.Icc (a+9) (a+d+5))]

end PlanarFalconer

end OAI
