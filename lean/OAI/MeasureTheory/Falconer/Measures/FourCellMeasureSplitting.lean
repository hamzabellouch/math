import OAI.MeasureTheory.Falconer.Measures.DyadicMeasureSplitting
import OAI.MeasureTheory.Falconer.Angular.AngularFourCellMass

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem angularFourCellMeasure_pi (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (row col : CellPath × CellPath)
    (s : Fin 4 → Set Plane) :
    angularFourCellMeasure Q₁ Q₂ ρ ν row col (Set.pi univ s) =
      (ρ.restrict (Q₁.descendant row.1).carrier (s 0) *
       ν.restrict (Q₂.descendant row.2).carrier (s 2)) *
      (ρ.restrict (Q₁.descendant col.1).carrier (s 1) *
       ν.restrict (Q₂.descendant col.2).carrier (s 3)) := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  change Measure.pi (fun i => (ρs i).restrict _) (Set.pi univ s) = _
  rw [Measure.pi_pi,Fin.prod_univ_four]
  dsimp [ρs]
  ring

theorem angularFourCellMeasure_split (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) :
    angularFourCellMeasure Q₁ Q₂ ρ ν (A,B) (A,B) =
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  change Measure.pi (fun i => (ρs i).restrict _) = _
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.finsetSum_apply,angularFourCellMeasure_pi]
  simp only [sourceProductVertices,Finset.sum_product,← Finset.mul_sum,← Finset.sum_mul]
  have he (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane) (P : CellPath)
      (t : Set Plane) :
      (∑ c ∈ (occupiedAnchorPaths (Q.descendant P) μ n).image (fun c => P++c),
        μ.restrict (Q.descendant c).carrier t) = μ.restrict (Q.descendant P).carrier t := by
    rw [← Measure.finsetSum_apply,occupied_absolute_measure_sum Q hQ]
  simp only [he Q₁ hQ₁,he Q₂ hQ₂,Fin.prod_univ_four]
  dsimp [ρs]
  ring

theorem angularFourCellMeasure_lintegral_split (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) (F : (Fin 4 → Plane) → ℝ≥0∞) :
    (∫⁻ x, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν (A,B) (A,B)) =
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ∫⁻ x, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
  rw [angularFourCellMeasure_split Q₁ Q₂ hQ₁ hQ₂ ρ ν A B n]
  simp only [lintegral_finsetSum_measure]

theorem angularFourCellMeasure_positive_rebin (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (h b : ℕ) (F : (Fin 4 → Plane) → ℝ≥0∞) :
    (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        ∫⁻ x, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col) =
    ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B b,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B b,
        ∫⁻ x, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
  rw [← angularFourCellMeasure_lintegral_split Q₁ Q₂ hQ₁ hQ₂,
    ← angularFourCellMeasure_lintegral_split Q₁ Q₂ hQ₁ hQ₂]

end PlanarFalconer

end OAI
