import OAI.MeasureTheory.Falconer.Graphs.ProductPairDegree
import OAI.MeasureTheory.Falconer.Graphs.ProductGraphIndices
import OAI.MeasureTheory.Falconer.Graphs.EligibleProductGraphSum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def productMatrixIndex (row col : CellPath × CellPath) (j b : ℕ) (plus : Bool) : GraphNonedgeIndex :=
  (((row.1,col.1),(row.2,col.2)),((j,b),plus))

noncomputable def productMatrixNeighbors (I : Finset GraphNonedgeIndex) (p j b : ℕ)
    (plus reverse : Bool) (row : CellPath × CellPath) : Finset (CellPath × CellPath) := by
  classical
  exact ((dyadicPaths p) ×ˢ (dyadicPaths p)).filter (fun col =>
    (if reverse then productMatrixIndex col row j b plus else productMatrixIndex row col j b plus) ∈ I)

theorem sourceProductGraphIndices_path_data
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (a n m : ℕ)
    (hA : A.length = a) (hB : B.length = a)
    {e : GraphNonedgeIndex}
    (he : e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    (l : Fin 4) :
    graphQuadPath e.1 l ∈ occupiedAnchorPaths (![Q₁,Q₁,Q₂,Q₂] l) (![ρ,ρ,ν,ν] l) (a+n) ∧
      (graphQuadPath e.1 l).take a = ![A,A,B,B] l := by
  classical
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  simp only [sourceProductRelativeIndices,Finset.mem_product] at hq
  have happ (Q : DyadicSquare) (μ : Measure Plane) (P c : CellPath)
      (hP : P.length = a) (hc : c ∈ occupiedAnchorPaths (Q.descendant P) μ n) :
      P++c ∈ occupiedAnchorPaths Q μ (a+n) ∧ (P++c).take a = P := by
    obtain ⟨hc,hpos⟩ := Finset.mem_filter.mp hc
    have hl := (mem_dyadicPaths _ _).mp hc
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨by simp [mem_dyadicPaths,hP,hl],by simpa only [DyadicSquare.descendant_append] using hpos⟩
    · simp [hP]
  fin_cases l
  · exact happ Q₁ ρ A q.1.1.1 hA hq.1.1.1
  · exact happ Q₁ ρ A q.1.1.2 hA hq.1.1.2
  · exact happ Q₂ ν B q.1.2.1 hB hq.1.2.1
  · exact happ Q₂ ν B q.1.2.2 hB hq.1.2.2

theorem productMatrix_cells (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath)
    (j b : ℕ) (plus : Bool) :
    graphQuadCells ![Q₁,Q₁,Q₂,Q₂] (productMatrixIndex row col j b plus).1 =
      productPairCells Q₁ Q₂ row col := by
  funext l
  fin_cases l <;> rfl

theorem productPairCells_reverse (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath) :
    productPairCells Q₁ Q₂ col row =
      ![productPairCells Q₁ Q₂ row col 1,productPairCells Q₁ Q₂ row col 0,
        productPairCells Q₁ Q₂ row col 3,productPairCells Q₁ Q₂ row col 2] := rfl

theorem productMatrixNeighbors_data
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n m N : ℕ) (sig : ℝ) (hA : A.length = a) (hB : B.length = a)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    (hret : ∀ e ∈ I, GraphRetainedEdge N sig (a+n) false e.2.2
      (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1) (rep e.2))
    (hel : ∀ e ∈ I, GraphProductIndexEligible ![ρ,ρ,ν,ν] ![Q₁,Q₁,Q₂,Q₂] ![β,β,γ,γ] m e)
    (j b : ℕ) (plus reverse : Bool) (row col : CellPath × CellPath)
    (hc : col ∈ productMatrixNeighbors I (a+n) j b plus reverse row) :
    col.1 ∈ occupiedAnchorPaths Q₁ ρ (a+n) ∧ col.1.take a = A ∧
    col.2 ∈ dyadicPaths (a+n) ∧
    GraphRetainedEdge N sig (a+n) false plus (productPairCells Q₁ Q₂ row col) (rep ((j,b),plus)) ∧
    AngularLabelEligible ρ (Q₁.descendant col.1).carrier β m j := by
  classical
  obtain ⟨hc,hi⟩ := Finset.mem_filter.mp hc
  have hlen := (Finset.mem_product.mp hc).2
  cases reverse
  · change productMatrixIndex row col j b plus ∈ I at hi
    have hp := sourceProductGraphIndices_path_data Q₁ Q₂ ρ ν A B a n m hA hB (hI hi) 1
    have hr := hret _ hi
    rw [productMatrix_cells] at hr
    exact ⟨hp.1,hp.2,hlen,hr,hel _ hi 1⟩
  · change productMatrixIndex col row j b plus ∈ I at hi
    have hp := sourceProductGraphIndices_path_data Q₁ Q₂ ρ ν A B a n m hA hB (hI hi) 0
    have hr := hret _ hi
    rw [productMatrix_cells,productPairCells_reverse] at hr
    have hr' := (graphRetainedProduct_reversal N sig (a+n) plus (productPairCells Q₁ Q₂ row col)
      (rep ((j,b),plus))).mp hr
    exact ⟨hp.1,hp.2,hlen,hr',hel _ hi 0⟩

noncomputable def sourceRetainedProductIndices
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n m N : ℕ) (sig : ℝ)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) : Finset GraphNonedgeIndex :=
  graphProductEligibleIndices
    (graphRetainedIndices
      (sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
      N sig (a+n) false ![Q₁,Q₁,Q₂,Q₂] rep)
    ![ρ,ρ,ν,ν] ![Q₁,Q₁,Q₂,Q₂] ![β,β,γ,γ] m

theorem sourceRetainedProductIndices_data
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n m N : ℕ) (sig : ℝ)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle)
    {e : GraphNonedgeIndex}
    (he : e ∈ sourceRetainedProductIndices Q₁ Q₂ ρ ν β γ A B a n m N sig rep) :
    e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B ∧
    GraphRetainedEdge N sig (a+n) false e.2.2 (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1) (rep e.2) ∧
    GraphProductIndexEligible ![ρ,ρ,ν,ν] ![Q₁,Q₁,Q₂,Q₂] ![β,β,γ,γ] m e := by
  classical
  obtain ⟨he,hel⟩ := Finset.mem_filter.mp he
  obtain ⟨he,hr⟩ := Finset.mem_filter.mp he
  exact ⟨he,hr,hel⟩

end PlanarFalconer

end OAI
