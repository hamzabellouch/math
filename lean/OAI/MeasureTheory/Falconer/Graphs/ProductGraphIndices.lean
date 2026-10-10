import OAI.MeasureTheory.Falconer.Graphs.GraphActualQuadCells
import OAI.MeasureTheory.Falconer.Graphs.GraphParentDiameter
import OAI.MeasureTheory.Falconer.Measures.DyadicIntegralSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def sourceProductRelativeIndices (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (n m : ℕ) : Finset GraphNonedgeIndex :=
  (((occupiedAnchorPaths X ρ n) ×ˢ (occupiedAnchorPaths X ρ n)) ×ˢ
    ((occupiedAnchorPaths Y ν n) ×ˢ (occupiedAnchorPaths Y ν n))) ×ˢ
      (((Finset.range m) ×ˢ (Finset.range m)) ×ˢ Finset.univ)

def sourceProductGraphIndex (A B : CellPath) (e : GraphNonedgeIndex) : GraphNonedgeIndex :=
  (((A++e.1.1.1,A++e.1.1.2),(B++e.1.2.1,B++e.1.2.2)),e.2)

theorem sourceProductGraphIndex_injective (A B : CellPath) :
    Function.Injective (sourceProductGraphIndex A B) := by
  rintro ⟨⟨⟨P,P'⟩,⟨Q,Q'⟩⟩,s⟩ ⟨⟨⟨V,V'⟩,⟨W,W'⟩⟩,t⟩ he
  simpa only [sourceProductGraphIndex,Prod.mk.injEq,List.append_cancel_left_eq] using he

noncomputable def sourceProductGraphIndices (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (n m : ℕ) (A B : CellPath) : Finset GraphNonedgeIndex := by
  classical
  exact (sourceProductRelativeIndices X Y ρ ν n m).image (sourceProductGraphIndex A B)

theorem sourceProductGraphIndices_subset {X Y : DyadicSquare} {ρ ν : Measure Plane}
    {a n m : ℕ} {A B : CellPath} (hA : A.length = a) (hB : B.length = a) :
    sourceProductGraphIndices X Y ρ ν n m A B ⊆ graphNonedgeIndices (a+n) m := by
  classical
  intro e he
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  simp only [sourceProductRelativeIndices,Finset.mem_product,Finset.mem_range,Finset.mem_univ,and_true] at hq
  have h0 := (Finset.mem_filter.mp hq.1.1.1).1
  have h1 := (Finset.mem_filter.mp hq.1.1.2).1
  have h2 := (Finset.mem_filter.mp hq.1.2.1).1
  have h3 := (Finset.mem_filter.mp hq.1.2.2).1
  simp only [mem_dyadicPaths] at h0 h1 h2 h3
  simp [graphNonedgeIndices,graphCellQuadIndices,sourceProductGraphIndex,mem_dyadicPaths,
    List.length_append,hA,hB,h0,h1,h2,h3,hq.2.1,hq.2.2]

theorem sourceProductGraphIndex_cells (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (e : GraphNonedgeIndex) (l : Fin 4) :
    graphQuadCells ![Q₁,Q₁,Q₂,Q₂] (sourceProductGraphIndex A B e).1 l =
      graphQuadCells ![Q₁.descendant A,Q₁.descendant A,Q₂.descendant B,Q₂.descendant B] e.1 l := by
  fin_cases l <;> simp [graphQuadCells,graphQuadPath,sourceProductGraphIndex,DyadicSquare.descendant_append]

theorem sourceProductGraphIndices_parent (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (A B : CellPath)
    (ρ ν : Measure Plane) (n m : ℕ) {e : GraphNonedgeIndex}
    (he : e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    (l : Fin 4) :
    (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier ⊆
      (graphSlotParent false (Q₁.descendant A) (Q₂.descendant B) l).carrier := by
  classical
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp he
  rw [sourceProductGraphIndex_cells]
  fin_cases l <;> simp only [graphSlotParent,Bool.false_eq_true,↓reduceIte,graphQuadCells,graphQuadPath] <;>
    apply DyadicSquare.descendant_subset <;>
    first | exact Q₁.descendant_side_pos hQ₁ A | exact Q₂.descendant_side_pos hQ₂ B

end PlanarFalconer

end OAI
