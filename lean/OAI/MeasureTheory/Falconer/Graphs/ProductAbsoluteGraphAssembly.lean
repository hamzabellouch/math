import OAI.MeasureTheory.Falconer.Graphs.ProductGraphEnergy
import OAI.MeasureTheory.Falconer.Graphs.GraphProfileCoefficient

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceProductGraphSum_absolute (v θ : ℝ) (Q₁ Q₂ : DyadicSquare)
    (A B : CellPath) (ρ ν : Measure Plane) (n : ℕ) (M₁ M₂ : ℝ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (Ψ : ℝ → ℝ) :
    (∑ e ∈ sourceProductRelativeIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ),
      graphOriginalTerm ![ρ,ρ,ν,ν]
        (fun l => (graphQuadCells ![Q₁.descendant A,Q₁.descendant A,Q₂.descendant B,Q₂.descendant B] e.1 l).carrier)
        ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ) =
    ∑ e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ) A B,
      graphOriginalTerm ![ρ,ρ,ν,ν] (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
        ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ := by
  classical
  rw [sourceProductGraphIndices,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e _
    simp only [sourceProductGraphIndex_cells]
    rfl
  · exact fun x _ y _ h => sourceProductGraphIndex_injective A B h

theorem sourceAngularH_absolute_graph_sum (a v : ℝ)
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (A B : CellPath)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ) {θ : ℝ} (hθ : 0 < θ)
    {Ma₁ Ma₂ Mp₁ Mp₂ : ℝ} (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hb₁ : Measurable (fun p : Plane × UnitCircle => b₁ p.1 p.2))
    (hb₂ : Measurable (fun p : Plane × UnitCircle => b₂ p.1 p.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hbound₂ : ∀ x dir, ‖b₂ x dir‖ ≤ B₂)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) :
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform ρ (Q₁.descendant A).carrier Ma₁ b₁ z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform ν (Q₂.descendant B).carrier Ma₂ b₂ z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) =
      ((2:ℝ)^(2*(v-a))) • (((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
        ∑ e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ) A B,
          graphOriginalTerm ![ρ,ρ,ν,ν] (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
            ![Mp₁,Mp₁,Mp₂,Mp₂] ![b₁,b₁,b₂,b₂] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ) := by
  have he := sourceAngularH_relative_graph_sum a v (Q₁.descendant A) (Q₂.descendant B)
    (Q₁.descendant_side_pos hQ₁ A) (Q₂.descendant_side_pos hQ₂ B) ρ ν n hθ
    hMa₁ hMa₂ hMp₁ hMp₂ b₁ b₂ hb₁ hb₂ hB₁ hB₂ hbound₁ hbound₂ hΨ hpos hs hC hc
  dsimp only at he ⊢
  rw [sourceProductGraphSum_absolute] at he
  exact he

theorem graphProfileCoefficient_product (N : ℕ) (m₁ m₂ : ℝ → ℝ) (a p : ℝ) :
    graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p =
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2)*
      ((((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) := by
  simp only [graphProfileCoefficient,Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  ring

end PlanarFalconer

end OAI
