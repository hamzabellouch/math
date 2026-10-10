import OAI.MeasureTheory.Falconer.Estimates.ProductOccupiedSum
import OAI.MeasureTheory.Falconer.Measures.DistanceMatrixSchur

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sourceParentGraphIndices_vertices (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (N n : ℕ) (sig t : ℝ) {e : GraphNonedgeIndex}
    (he : e ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B) :
    (e.1.1.1,e.1.2.1) ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n ∧
    (e.1.1.2,e.1.2.2) ∈ sourceProductVertices Q₂ Q₁ ν ρ B A n := by
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨heP,heQ,_⟩ := sourceParentBinLabels_spec (Finset.mem_product.mp hef).1
  obtain ⟨hfP,hfQ,_⟩ := sourceParentBinLabels_spec (Finset.mem_product.mp hef).2
  constructor
  · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,heP,rfl⟩,
      Finset.mem_image.mpr ⟨_,hfQ,rfl⟩⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,heQ,rfl⟩,
      Finset.mem_image.mpr ⟨_,hfP,rfl⟩⟩

theorem sourceParentGraphIndices_sign (X Y : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (N n : ℕ) (sig t : ℝ) {e : GraphNonedgeIndex}
    (he : e ∈ sourceParentGraphIndices N sig t X Y ρ ν n A B) : e.2.2 = true := by
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp he
  rfl

theorem sourceProductVertices_swap_sum (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) {α : Type*} [AddCommMonoid α]
    (F : CellPath → CellPath → α) :
    (∑ col ∈ sourceProductVertices Q₂ Q₁ ν ρ B A n, F col.1 col.2) =
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, F row.2 row.1 := by
  simp only [sourceProductVertices,Finset.sum_product]
  exact Finset.sum_comm

theorem distance_matrix_sum_restrict {p : ℕ} (I : Finset GraphNonedgeIndex)
    (C D : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hD : D ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hvertices : ∀ e ∈ I, (e.1.1.1,e.1.2.1) ∈ C ∧ (e.1.1.2,e.1.2.2) ∈ D)
    (j b : ℕ) (plus : Bool) {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
      ∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if distanceMatrixIndex row col j b plus ∈ I then F (distanceMatrixIndex row col j b plus) else 0) =
    ∑ row ∈ C, ∑ col ∈ D,
      if distanceMatrixIndex row col j b plus ∈ I then F (distanceMatrixIndex row col j b plus) else 0 := by
  classical
  have hcol (row : CellPath × CellPath) :
      (∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if distanceMatrixIndex row col j b plus ∈ I then F (distanceMatrixIndex row col j b plus) else 0) =
      ∑ col ∈ D, if distanceMatrixIndex row col j b plus ∈ I then F (distanceMatrixIndex row col j b plus) else 0 := by
    symm
    apply Finset.sum_subset hD
    intro col _ hn
    have hi : distanceMatrixIndex row col j b plus ∉ I := fun hi => hn (hvertices _ hi).2
    simp [hi]
  simp_rw [hcol]
  symm
  apply Finset.sum_subset hC
  intro row _ hn
  apply Finset.sum_eq_zero
  intro col _
  have hi : distanceMatrixIndex row col j b plus ∉ I := fun hi => hn (hvertices _ hi).1
  simp [hi]

theorem source_distance_graph_sum_occupied (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (N a n : ℕ) (sig t : ℝ) (hA : A.length = a) (hB : B.length = a)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ e ∈ I, F e) =
    ∑ j ∈ Finset.range (angularBinCount (graphUncappedAngularScale N sig t)),
      ∑ b ∈ Finset.range (angularBinCount (graphUncappedAngularScale N sig t)),
        ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ∑ col ∈ sourceProductVertices Q₂ Q₁ ν ρ B A n,
            if distanceMatrixIndex row col j b true ∈ I then F (distanceMatrixIndex row col j b true) else 0 := by
  classical
  rw [product_graph_sum_bins I (hI.trans (sourceParentGraphIndices_subset hA hB)) F]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  have hz (row col : CellPath × CellPath) : productMatrixIndex row col j b false ∉ I := by
    intro he
    have hs := sourceParentGraphIndices_sign _ _ _ _ _ _ _ _ _ _ (hI he)
    exact Bool.noConfusion hs
  simp only [Fintype.sum_bool,hz,↓reduceIte,Finset.sum_const_zero,add_zero]
  exact distance_matrix_sum_restrict I _ _
    (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB)
    (sourceProductVertices_subset Q₂ Q₁ ν ρ B A a n hB hA)
    (fun e he => sourceParentGraphIndices_vertices Q₁ Q₂ ρ ν A B N n sig t (hI he)) j b true F

end PlanarFalconer

end OAI
