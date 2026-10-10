import OAI.MeasureTheory.Falconer.Measures.ProductMatrixSchur

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def sourceProductVertices (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) : Finset (CellPath × CellPath) :=
  ((occupiedAnchorPaths (Q₁.descendant A) ρ n).image (fun c => A++c)) ×ˢ
    ((occupiedAnchorPaths (Q₂.descendant B) ν n).image (fun c => B++c))

theorem sourceProductVertices_subset (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a) :
    sourceProductVertices Q₁ Q₂ ρ ν A B n ⊆ (dyadicPaths (a+n)) ×ˢ (dyadicPaths (a+n)) := by
  classical
  intro c hc
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hc
  obtain ⟨x,hx,hx'⟩ := Finset.mem_image.mp h1
  obtain ⟨y,hy,hy'⟩ := Finset.mem_image.mp h2
  have hlx := (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hx).1
  have hly := (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hy).1
  rw [Finset.mem_product,← hx',← hy']
  simp [mem_dyadicPaths,hA,hB,hlx,hly]

theorem sourceProductVertices_card (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) :
    (sourceProductVertices Q₁ Q₂ ρ ν A B n).card =
      (occupiedAnchorPaths (Q₁.descendant A) ρ n).card*
      (occupiedAnchorPaths (Q₂.descendant B) ν n).card := by
  rw [sourceProductVertices,Finset.card_product]
  congr 1 <;> apply Finset.card_image_of_injective <;>
    intro c d he <;> exact List.append_cancel_left he

theorem sourceProductGraphIndices_vertices (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n m : ℕ) {e : GraphNonedgeIndex}
    (he : e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B) :
    (e.1.1.1,e.1.2.1) ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n ∧
    (e.1.1.2,e.1.2.2) ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  simp only [sourceProductRelativeIndices,Finset.mem_product] at hq
  constructor
  · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,hq.1.1.1,rfl⟩,
      Finset.mem_image.mpr ⟨_,hq.1.2.1,rfl⟩⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,hq.1.1.2,rfl⟩,
      Finset.mem_image.mpr ⟨_,hq.1.2.2,rfl⟩⟩

theorem product_matrix_schur_on (I : Finset GraphNonedgeIndex) (p j b : ℕ) (θ : ℝ)
    (plus : Bool) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (u v : CellPath × CellPath → ℝ) (d : ℝ)
    (hdegree : ∀ (reverse : Bool) (row : CellPath × CellPath),
      ((activeProductMatrixNeighbors I p j b θ plus reverse row).card : ℝ) ≤ d) :
    let H := graphSupportedProductIndices I θ
    (∑ row ∈ C, ∑ col ∈ C, if productMatrixIndex row col j b plus ∈ H then u row*v col else 0) ≤
      d/2*((∑ row ∈ C, u row^2)+(∑ col ∈ C, v col^2)) := by
  classical
  dsimp only
  apply finset_bipartite_schur
  · intro row _
    apply le_trans _ (hdegree false row)
    rw [activeProductMatrixNeighbors_eq_supported]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro col hc
    obtain ⟨hc,hi⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨hC hc,hi⟩
  · intro col _
    apply le_trans _ (hdegree true col)
    rw [activeProductMatrixNeighbors_eq_supported]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro row hr
    obtain ⟨hr,hi⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hC hr,hi⟩

end PlanarFalconer

end OAI
