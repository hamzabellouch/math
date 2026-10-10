import OAI.MeasureTheory.Falconer.Graphs.ParentGraphEnergy
import OAI.MeasureTheory.Falconer.Graphs.ParentGraphIndices
import OAI.MeasureTheory.Falconer.Graphs.GraphProfileCoefficient

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceParentGraphTerm_absolute (N : ℕ) (sig t v : ℝ) (Q₁ Q₂ : DyadicSquare)
    (A B : CellPath) (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (Ψ : ℝ → ℝ) (e f : ParentDistanceBinLabel) :
    sourceParentGraphTerm N sig t v (Q₁.descendant A) (Q₂.descendant B) ρ ν M₁ M₂ b₁ b₂ Ψ e f =
      let q := sourceParentGraphIndex A B (e,f)
      graphOriginalTerm ![ρ,ν,ν,ρ]
        (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] q.1 l).carrier)
        ![M₁,M₂,M₂,M₁] ![b₁,b₂,b₂,b₁] true q.2.2
        (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B))
        (graphUncappedAngularScale N sig t) v q.2.1.1 q.2.1.2 Ψ := by
  dsimp only
  have hc : (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] (sourceParentGraphIndex A B (e,f)).1 l).carrier) =
      ![((Q₁.descendant A).descendant e.1.1).carrier,((Q₂.descendant B).descendant e.1.2).carrier,
        ((Q₂.descendant B).descendant f.1.2).carrier,((Q₁.descendant A).descendant f.1.1).carrier] := by
    funext l
    rw [sourceParentGraphIndex_cells]
    fin_cases l <;> rfl
  rw [hc]
  rfl

theorem sourceParentGraphSum_absolute (N n : ℕ) (sig t v : ℝ) (Q₁ Q₂ : DyadicSquare)
    (A B : CellPath) (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (Ψ : ℝ → ℝ) :
    (∑ e ∈ sourceParentBinLabels N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n,
      ∑ f ∈ sourceParentBinLabels N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n,
        sourceParentGraphTerm N sig t v (Q₁.descendant A) (Q₂.descendant B) ρ ν M₁ M₂ b₁ b₂ Ψ e f) =
    ∑ q ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B,
      graphOriginalTerm ![ρ,ν,ν,ρ] (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] q.1 l).carrier)
        ![M₁,M₂,M₂,M₁] ![b₁,b₂,b₂,b₁] true q.2.2
        (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B))
        (graphUncappedAngularScale N sig t) v q.2.1.1 q.2.1.2 Ψ := by
  classical
  rw [sourceParentGraphIndices,Finset.sum_image]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    exact sourceParentGraphTerm_absolute N sig t v Q₁ Q₂ A B ρ ν M₁ M₂ b₁ b₂ Ψ e f
  · exact fun x _ y _ h => sourceParentGraphIndex_injective A B h

theorem sourceParentRetainedEnergy_absolute_graph_sum (N : ℕ) (sig t a v : ℝ)
    (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ)
    {Ma₁ Ma₂ Mp₁ Mp₂ : ℝ} (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W) :
    (sourceRadialSquareEnergy a v Ψ (sourceParentRetainedF N sig t (Q₁.descendant A) (Q₂.descendant B)
      ρ ν n Ma₁ Ma₂ b₁ b₂) : ℂ) =
      ((2:ℝ)^(2*(v-a))) • (((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
        ∑ q ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B,
          graphOriginalTerm ![ρ,ν,ν,ρ] (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] q.1 l).carrier)
            ![Mp₁,Mp₂,Mp₂,Mp₁] ![b₁,b₂,b₂,b₁] true q.2.2
            (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B))
            (graphUncappedAngularScale N sig t) v q.2.1.1 q.2.1.2 Ψ) := by
  rw [sourceParentRetainedEnergy_graph_sum N sig t a v _ _ ρ ν n hMa₁ hMa₂ b₁ b₂
    h₁ h₂ hB₁ hB₂ hb₁ hb₂ hΨ hpos hs hW hw]
  simp_rw [sourceParentGraphTerm_profile_ratios N sig t v _ _ ρ ν Ma₁ Ma₂ Mp₁ Mp₂ hMp₁ hMp₂,
    ← Finset.smul_sum]
  rw [sourceParentGraphSum_absolute]

theorem graphProfileCoefficient_distance (N : ℕ) (m₁ m₂ : ℝ → ℝ) (a p : ℝ) :
    graphProfileCoefficient N ![m₁,m₂,m₂,m₁] a p =
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2)*
      ((((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) := by
  simp only [graphProfileCoefficient,Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  ring

end PlanarFalconer

end OAI
