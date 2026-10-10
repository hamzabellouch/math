import OAI.MeasureTheory.Falconer.Estimates.ProductOccupiedSum
import OAI.MeasureTheory.Falconer.Estimates.ProductWeightSum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem product_graph_pointwise_bound
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (a n m : ℕ)
    (hA : A.length = a) (hB : B.length = a) (hm : 0 < m)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    (θ d : ℝ)
    (hdegree : ∀ j k s reverse row,
      ((activeProductMatrixNeighbors I (a+n) j k θ s reverse row).card : ℝ) ≤ d)
    (U V : CellPath → ℂ) (u w : UnitCircle) :
    ‖∑ e ∈ graphSupportedProductIndices I θ,
      graphProductWeight e.2.2 m e.2.1.1 e.2.1.2 (u,w) *
        (U e.1.1.1*conj (U e.1.1.2))*(V e.1.2.1*conj (V e.1.2.2))‖ ≤
      d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, ‖U row.1‖^2*‖V row.2‖^2 := by
  classical
  let C := sourceProductVertices Q₁ Q₂ ρ ν A B n
  let H := graphSupportedProductIndices I θ
  let F := fun e : GraphNonedgeIndex => graphProductWeight e.2.2 m e.2.1.1 e.2.1.2 (u,w) *
    (U e.1.1.1*conj (U e.1.1.2))*(V e.1.2.1*conj (V e.1.2.2))
  have hh : H ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B :=
    (Finset.filter_subset _ _).trans hI
  change ‖∑ e ∈ H, F e‖ ≤ _
  rw [source_product_graph_sum_occupied Q₁ Q₂ ρ ν A B a n m hA hB H hh F]
  calc
    _ ≤ ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ∑ s : Bool,
        ‖∑ row ∈ C, ∑ col ∈ C, if productMatrixIndex row col j k s ∈ H
          then F (productMatrixIndex row col j k s) else 0‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ∑ s : Bool,
        ‖graphProductWeight s m j k (u,w)‖*d*(∑ row ∈ C, ‖U row.1‖^2*‖V row.2‖^2) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro s _
      exact product_matrix_complex_bound_on I (a+n) j k θ s C
        (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB)
        U V (graphProductWeight s m j k (u,w)) d (hdegree j k s)
    _ = _ := by
      simp only [← Finset.sum_mul,graphProductWeight_norm_total hm,one_mul,C]

end PlanarFalconer

end OAI
