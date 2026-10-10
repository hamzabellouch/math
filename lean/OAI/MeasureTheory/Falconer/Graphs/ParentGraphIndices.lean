import OAI.MeasureTheory.Falconer.Recursion.ParentBinFamily
import OAI.MeasureTheory.Falconer.Graphs.GraphActualQuadCells
import OAI.MeasureTheory.Falconer.Graphs.GraphParentDiameter

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def sourceParentGraphIndex (A B : CellPath) (ef : ParentDistanceBinLabel × ParentDistanceBinLabel) :
    GraphNonedgeIndex :=
  (((A++ef.1.1.1,B++ef.1.1.2),(B++ef.2.1.2,A++ef.2.1.1)),((ef.1.2,ef.2.2),true))

theorem sourceParentGraphIndex_injective (A B : CellPath) : Function.Injective (sourceParentGraphIndex A B) := by
  classical
  rintro ⟨⟨⟨P,Q⟩,j⟩,⟨⟨P',Q'⟩,k⟩⟩ ⟨⟨⟨S,T⟩,l⟩,⟨⟨S',T'⟩,m⟩⟩ h
  simp only [sourceParentGraphIndex,Prod.mk.injEq,List.append_cancel_left_eq] at h
  obtain ⟨⟨⟨hP,hQ⟩,⟨hQ',hP'⟩⟩,⟨⟨hj,hk⟩,_⟩⟩ := h
  subst S; subst T; subst S'; subst T'; subst l; subst m
  rfl

noncomputable def sourceParentGraphIndices (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (n : ℕ) (A B : CellPath) : Finset GraphNonedgeIndex := by
  classical
  exact ((sourceParentBinLabels N sig t X Y ρ ν n) ×ˢ
    (sourceParentBinLabels N sig t X Y ρ ν n)).image (sourceParentGraphIndex A B)

theorem sourceParentGraphIndex_mem {N a n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {A B : CellPath} (hA : A.length = a) (hB : B.length = a)
    {e f : ParentDistanceBinLabel} (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n)
    (hf : f ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    sourceParentGraphIndex A B (e,f) ∈ graphNonedgeIndices (a+n)
      (angularBinCount (graphUncappedAngularScale N sig t)) := by
  classical
  obtain ⟨heP,heQ⟩ := sourceParentBinLabels_length he
  obtain ⟨hfP,hfQ⟩ := sourceParentBinLabels_length hf
  have hej := sourceParentBinLabels_bin_lt he
  have hfj := sourceParentBinLabels_bin_lt hf
  simp [graphNonedgeIndices,graphCellQuadIndices,sourceParentGraphIndex,mem_dyadicPaths,
    List.length_append,hA,hB,heP,heQ,hfP,hfQ,hej,hfj]

theorem sourceParentGraphIndices_subset {N a n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {A B : CellPath} (hA : A.length = a) (hB : B.length = a) :
    sourceParentGraphIndices N sig t X Y ρ ν n A B ⊆ graphNonedgeIndices (a+n)
      (angularBinCount (graphUncappedAngularScale N sig t)) := by
  classical
  intro q hq
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp hq
  exact sourceParentGraphIndex_mem hA hB (Finset.mem_product.mp hef).1 (Finset.mem_product.mp hef).2

theorem sourceParentGraphIndex_cells (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (e f : ParentDistanceBinLabel) (l : Fin 4) :
    graphQuadCells ![Q₁,Q₂,Q₂,Q₁] (sourceParentGraphIndex A B (e,f)).1 l =
      ![((Q₁.descendant A).descendant e.1.1),((Q₂.descendant B).descendant e.1.2),
        ((Q₂.descendant B).descendant f.1.2),((Q₁.descendant A).descendant f.1.1)] l := by
  fin_cases l <;> simp [graphQuadCells,graphQuadPath,sourceParentGraphIndex,DyadicSquare.descendant_append]

theorem sourceParentGraphIndices_parent (Q₁ Q₂ : DyadicSquare) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (A B : CellPath) (N n : ℕ) (sig t : ℝ) (ρ ν : Measure Plane)
    {q : GraphNonedgeIndex}
    (hq : q ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    (l : Fin 4) :
    (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] q.1 l).carrier ⊆
      (graphSlotParent true (Q₁.descendant A) (Q₂.descendant B) l).carrier := by
  classical
  obtain ⟨⟨e,f⟩,_,rfl⟩ := Finset.mem_image.mp hq
  rw [sourceParentGraphIndex_cells]
  fin_cases l <;> simp only [graphSlotParent,↓reduceIte] <;>
    apply DyadicSquare.descendant_subset <;>
    first | exact Q₁.descendant_side_pos hQ₁ A | exact Q₂.descendant_side_pos hQ₂ B

end PlanarFalconer

end OAI
