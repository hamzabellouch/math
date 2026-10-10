import OAI.MeasureTheory.Falconer.Measures.FourCellMeasureSplitting
import OAI.MeasureTheory.Falconer.Angular.AngularFarSeparation

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

def angularSeparated (Q₁ Q₂ : DyadicSquare) (b : ℕ)
    (row col : CellPath × CellPath) : Prop :=
  (100*(2:ℝ)^(-(b:ℝ)) ≤ dist (Q₁.descendant row.1).center (Q₁.descendant col.1).center ∧
    dist (Q₁.descendant row.1).center (Q₁.descendant col.1).center ≤ 2000*(2:ℝ)^(-(b:ℝ))) ∧
  (100*(2:ℝ)^(-(b:ℝ)) ≤ dist (Q₂.descendant row.2).center (Q₂.descendant col.2).center ∧
    dist (Q₂.descendant row.2).center (Q₂.descendant col.2).center ≤ 2000*(2:ℝ)^(-(b:ℝ)))

theorem angular_shell_lintegral_zero_of_not_separated (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (b : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths b) ×ˢ (dyadicPaths b))
    (hc : col ∈ (dyadicPaths b) ×ˢ (dyadicPaths b))
    (hn : ¬ angularSeparated Q₁ Q₂ b row col) (F : (Fin 4 → Plane) → ℝ≥0∞) :
    (∫⁻ x in angularLengthShell b, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col) = 0 := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier]
  have hae := graph_four_spatial_ae_carrier ρs X
    (by intro i; fin_cases i <;> exact DyadicSquare.measurable _)
  rw [← lintegral_indicator (measurable_angularLengthShell b)]
  calc
    _ = ∫⁻ _ : Fin 4 → Plane, 0 ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
      apply lintegral_congr_ae
      filter_upwards [hae] with x hx
      apply Set.indicator_of_notMem
      intro hs
      have hl := angularLengthShell_lengths b hs
      apply hn
      constructor
      · exact comparable_dyadic_cells_strong_separation Q₁ Q₁ hQ₁ hQ₁ b row.1 col.1
          ((mem_dyadicPaths b _).mp (Finset.mem_product.mp hr).1)
          ((mem_dyadicPaths b _).mp (Finset.mem_product.mp hc).1)
          (hx 0) (hx 1) hl.1.1 hl.1.2
      · exact comparable_dyadic_cells_strong_separation Q₂ Q₂ hQ₂ hQ₂ b row.2 col.2
          ((mem_dyadicPaths b _).mp (Finset.mem_product.mp hr).2)
          ((mem_dyadicPaths b _).mp (Finset.mem_product.mp hc).2)
          (hx 2) (hx 3) hl.2.1 hl.2.2
    _ = 0 := by simp

theorem angular_shell_positive_rebin (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a h n : ℕ) (hA : A.length = a) (hB : B.length = a)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (F : (Fin 4 → Plane) → ℝ≥0∞) :
    (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        if G row col then
          ∫⁻ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0) ≤
    ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        if angularSeparated Q₁ Q₂ (a+n) row col then
          ∫⁻ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0 := by
  have hp₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hp₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  calc
    _ ≤ ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
          ∫⁻ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
      apply Finset.sum_le_sum
      intro row _
      apply Finset.sum_le_sum
      intro col _
      split_ifs <;> simp
    _ = ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ∫⁻ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
      simp_rw [← lintegral_indicator (measurable_angularLengthShell (a+n))]
      exact angularFourCellMeasure_positive_rebin Q₁ Q₂ hp₁ hp₂ ρ ν A B h n _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro row hr
      apply Finset.sum_congr rfl
      intro col hc
      by_cases hs : angularSeparated Q₁ Q₂ (a+n) row col
      · simp [hs]
      · simp only [hs,↓reduceIte]
        exact angular_shell_lintegral_zero_of_not_separated Q₁ Q₂ hQ₁ hQ₂ ρ ν (a+n) row col
          (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB hr)
          (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB hc) hs F

end PlanarFalconer

end OAI
