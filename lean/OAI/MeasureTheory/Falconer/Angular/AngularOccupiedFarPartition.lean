import OAI.MeasureTheory.Falconer.Angular.AngularOriginalFarPartition
import OAI.MeasureTheory.Falconer.Angular.AngularFarSpatialSum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sourceProductVertices_parent (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) {row : CellPath × CellPath}
    (hr : row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n) :
    (Q₁.descendant row.1).carrier ⊆ (Q₁.descendant A).carrier ∧
    (Q₂.descendant row.2).carrier ⊆ (Q₂.descendant B).carrier := by
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hr
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp h1
  obtain ⟨d,_,hd⟩ := Finset.mem_image.mp h2
  rw [← hc,← hd,DyadicSquare.descendant_append,DyadicSquare.descendant_append]
  exact ⟨(Q₁.descendant A).descendant_subset (Q₁.descendant_side_pos hQ₁ A) c,
    (Q₂.descendant B).descendant_subset (Q₂.descendant_side_pos hQ₂ B) d⟩

theorem angular_far_contribution_partition (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (Ma₁ Ma₂ : ℝ) {Mp₁ Mp₂ : ℝ} (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂) :
    angularCellContribution Q₁ Q₂ ρ ν A B n a v Ψ Ma₁ Ma₂ Mp₁ Mp₂ β γ
      (fun row col => ¬ angularNear Q₁ Q₂ (a+n) row col) =
    (((2:ℝ)^(2*(v-a)))/(Ma₁^2*Ma₂^2)) •
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          if ¬ angularNear Q₁ Q₂ (a+n) row col then
            angularSpatialPiece Q₁ Q₂ ρ ν β γ row col v Ψ angularLengthLeft +
            angularSpatialPiece Q₁ Q₂ ρ ν β γ row col v Ψ angularLengthRight +
            ∑ b ∈ Finset.Icc (a+9) (a+n+5),
              angularSpatialPiece Q₁ Q₂ ρ ν β γ row col v Ψ (angularLengthShell b)
          else 0 := by
  rw [angular_contribution_spatial_sum Q₁ Q₂ ρ ν A B n a v hΨ hpos hs hW hw
    Ma₁ Ma₂ hMp₁ hMp₂ β γ hβ hγ hD₁ hD₂ hbβ hbγ]
  congr 1
  apply Finset.sum_congr rfl
  intro row hr
  apply Finset.sum_congr rfl
  intro col hc
  by_cases hf : ¬ angularNear Q₁ Q₂ (a+n) row col
  · simp only [hf]
    have hqr : 0 < Q₁.side := by simpa only [hQ₁] using (zero_lt_one : (0 : ℝ) < 1)
    have hqs : 0 < Q₂.side := by simpa only [hQ₂] using (zero_lt_one : (0 : ℝ) < 1)
    have hp := sourceProductVertices_parent Q₁ Q₂ hqr hqs ρ ν A B n hr
    have hq := sourceProductVertices_parent Q₁ Q₂ hqr hqs ρ ν A B n hc
    exact angular_original_far_partition Q₁ Q₂ hQ₁ hQ₂ ρ ν A B a (a+n) hA hB row col
      (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB hr)
      (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB hc)
      hf hp.1 hq.1 hp.2 hq.2 β γ hβ hγ hD₁ hD₂ hbβ hbγ v hΨ hs hW
      (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t)
  · simp only [hf,↓reduceIte]

end PlanarFalconer

end OAI
