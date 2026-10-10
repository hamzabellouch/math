import OAI.MeasureTheory.Falconer.Estimates.ProductMatrixReindex
import OAI.MeasureTheory.Falconer.Estimates.ProductOccupiedIntegrand

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem product_matrix_sum_restrict {p : ℕ} (I : Finset GraphNonedgeIndex)
    (C : Finset (CellPath × CellPath)) (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hvertices : ∀ e ∈ I, (e.1.1.1,e.1.2.1) ∈ C ∧ (e.1.1.2,e.1.2.2) ∈ C)
    (j b : ℕ) (plus : Bool) {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
      ∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0) =
    ∑ row ∈ C, ∑ col ∈ C,
      if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
  classical
  have hcol (row : CellPath × CellPath) :
      (∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0) =
      ∑ col ∈ C, if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
    symm
    apply Finset.sum_subset hC
    intro col _ hn
    have hi : productMatrixIndex row col j b plus ∉ I := fun hi => hn (hvertices _ hi).2
    simp [hi]
  simp_rw [hcol]
  symm
  apply Finset.sum_subset hC
  intro row _ hn
  apply Finset.sum_eq_zero
  intro col _
  have hi : productMatrixIndex row col j b plus ∉ I := fun hi => hn (hvertices _ hi).1
  simp [hi]

theorem source_product_graph_sum_occupied (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (a n m : ℕ) (hA : A.length = a) (hB : B.length = a)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ e ∈ I, F e) =
    ∑ j ∈ Finset.range m, ∑ b ∈ Finset.range m, ∑ plus : Bool,
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
  rw [product_graph_sum_bins I (hI.trans (sourceProductGraphIndices_subset hA hB)) F]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro plus _
  exact product_matrix_sum_restrict I _ (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB)
    (fun e he => sourceProductGraphIndices_vertices Q₁ Q₂ ρ ν A B n m (hI he)) j b plus F

end PlanarFalconer

end OAI
