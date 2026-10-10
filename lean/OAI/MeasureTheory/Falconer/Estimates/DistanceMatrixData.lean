import OAI.MeasureTheory.Falconer.Estimates.DistanceEligibleIndices
import OAI.MeasureTheory.Falconer.Estimates.DistanceActivityStrip
import OAI.MeasureTheory.Falconer.Graphs.DistancePairDegree

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def distanceMatrixIndex (row col : CellPath × CellPath) (j b : ℕ) (plus : Bool) : GraphNonedgeIndex :=
  (((row.1,col.1),(row.2,col.2)),((j,b),plus))

noncomputable def distanceMatrixNeighbors (I : Finset GraphNonedgeIndex) (p j b : ℕ)
    (plus reverse : Bool) (row : CellPath × CellPath) : Finset (CellPath × CellPath) := by
  classical
  exact ((dyadicPaths p) ×ˢ (dyadicPaths p)).filter (fun col =>
    (if reverse then distanceMatrixIndex col row j b plus else distanceMatrixIndex row col j b plus) ∈ I)

theorem sourceParentGraphIndices_occupied
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (N a n : ℕ) (sig t : ℝ)
    (hA : A.length = a) (hB : B.length = a)
    {e : GraphNonedgeIndex}
    (he : e ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    (l : Fin 4) :
    graphQuadPath e.1 l ∈ occupiedAnchorPaths (![Q₁,Q₂,Q₂,Q₁] l) (![ρ,ν,ν,ρ] l) (a+n) := by
  classical
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨he,hf⟩ := Finset.mem_product.mp hef
  obtain ⟨heP,heQ,_⟩ := sourceParentBinLabels_spec he
  obtain ⟨hfP,hfQ,_⟩ := sourceParentBinLabels_spec hf
  have happ (Q : DyadicSquare) (μ : Measure Plane) (P c : CellPath)
      (hP : P.length = a) (hc : c ∈ occupiedAnchorPaths (Q.descendant P) μ n) :
      P++c ∈ occupiedAnchorPaths Q μ (a+n) := by
    obtain ⟨hc,hpos⟩ := Finset.mem_filter.mp hc
    have hl := (mem_dyadicPaths _ _).mp hc
    apply Finset.mem_filter.mpr
    exact ⟨by simp [mem_dyadicPaths,hP,hl],by simpa only [DyadicSquare.descendant_append] using hpos⟩
  fin_cases l
  · exact happ Q₁ ρ A e.1.1 hA heP
  · exact happ Q₂ ν B e.1.2 hB heQ
  · exact happ Q₂ ν B f.1.2 hB hfQ
  · exact happ Q₁ ρ A f.1.1 hA hfP

theorem sourceParentGraphIndices_activity
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (N n : ℕ) (sig t : ℝ)
    {e : GraphNonedgeIndex}
    (he : e ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B) :
    let P := graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1
    let θ := graphUncappedAngularScale N sig t
    let X := Q₁.descendant A
    let Y := Q₂.descendant B
    AngularBinActive (angularBinCount θ) e.2.1.1 (sourceCenteredCellDirection X Y (P 0) (P 1)) (3*θ) ∧
    AngularBinActive (angularBinCount θ) e.2.1.2 (sourceCenteredCellDirection X Y (P 3) (P 2)) (3*θ) := by
  classical
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp he
  dsimp only
  simp only [sourceParentGraphIndex_cells]
  exact ⟨sourceParentBinLabels_activity (Finset.mem_product.mp hef).1,
    sourceParentBinLabels_activity (Finset.mem_product.mp hef).2⟩

theorem distanceMatrix_cells (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath)
    (j b : ℕ) (plus : Bool) :
    graphQuadCells ![Q₁,Q₂,Q₂,Q₁] (distanceMatrixIndex row col j b plus).1 =
      distancePairCells Q₁ Q₂ row col := by
  funext l
  fin_cases l <;> rfl

theorem graphRetainedDistance_reversal (N : ℕ) (sig p : ℝ) (plus : Bool)
    (P : Fin 4 → DyadicSquare) (q : UnitCircle × UnitCircle) :
    GraphRetainedEdge N sig p true plus ![P 1,P 0,P 3,P 2] q ↔
      GraphRetainedEdge N sig p true plus P q := by
  have he : ∀ (z s : ℝ) (v w : Plane), graphA z (-v)+s • graphB z (-w) = -(graphA z v+s • graphB z w) := by
    intro z s v w
    ext l
    fin_cases l <;> simp [graphA,graphB,quarterTurn] <;> ring
  simp only [GraphRetainedEdge,Bool.true_eq_false,false_implies, and_true,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [show (P 1).center-(P 0).center = -((P 0).center-(P 1).center) by abel,
    show (P 3).center-(P 2).center = -((P 2).center-(P 3).center) by abel,he,norm_neg]

noncomputable def sourceRetainedDistanceIndices
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n N : ℕ) (sig t θ : ℝ)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) : Finset GraphNonedgeIndex :=
  graphDistanceEligibleIndices (graphRetainedIndices
    (sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    N sig (a+n) true ![Q₁,Q₂,Q₂,Q₁] rep)
    Q₁ Q₂ ρ ν β γ (angularBinCount θ) (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B))

theorem sourceRetainedDistanceIndices_data
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n N : ℕ) (sig t θ : ℝ)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) {e : GraphNonedgeIndex}
    (he : e ∈ sourceRetainedDistanceIndices Q₁ Q₂ ρ ν β γ A B a n N sig t θ rep) :
    e ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B ∧
    GraphRetainedEdge N sig (a+n) true e.2.2 (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1) (rep e.2) ∧
    GraphDistanceIndexEligible Q₁ Q₂ ρ ν β γ (angularBinCount θ)
      (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B)) e := by
  classical
  obtain ⟨he,hel⟩ := Finset.mem_filter.mp he
  obtain ⟨he,hr⟩ := Finset.mem_filter.mp he
  exact ⟨he,hr,hel⟩

end PlanarFalconer

end OAI
