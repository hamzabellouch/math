import OAI.MeasureTheory.Falconer.Estimates.DistanceOccupiedSum
import OAI.MeasureTheory.Falconer.Estimates.DistanceWeightSum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem distance_graph_pointwise_bound
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (N a n : ℕ)
    (sig t : ℝ) (hA : A.length = a) (hB : B.length = a)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    {θ : ℝ} (hθ : 0 < θ) (hscale : θ = graphUncappedAngularScale N sig t)
    (axis d : ℝ) (hd : 0 ≤ d)
    (hdegree : ∀ j k s reverse row,
      ((activeDistanceMatrixNeighbors I (a+n) j k θ axis s reverse row).card : ℝ) ≤ d)
    (U V : CellPath → UnitCircle → ℂ) (u w : UnitCircle) :
    ‖∑ e ∈ graphSupportedDistanceIndices I θ axis,
      graphRotatedDistanceWeight axis (angularBinCount θ) e.2.1.1 e.2.1.2 (u,w) *
        (U e.1.1.1 u*conj (V e.1.1.2 u))*(V e.1.2.1 w*conj (U e.1.2.2 w))‖ ≤
      d/2 * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (‖U row.1 u‖^2*‖V row.2 w‖^2 + ‖V row.2 u‖^2*‖U row.1 w‖^2) := by
  classical
  let C := sourceProductVertices Q₁ Q₂ ρ ν A B n
  let D := sourceProductVertices Q₂ Q₁ ν ρ B A n
  let H := graphSupportedDistanceIndices I θ axis
  let F := fun e : GraphNonedgeIndex => graphRotatedDistanceWeight axis (angularBinCount θ) e.2.1.1 e.2.1.2 (u,w) *
    (U e.1.1.1 u*conj (V e.1.1.2 u))*(V e.1.2.1 w*conj (U e.1.2.2 w))
  let S := d/2 * ((∑ row ∈ C, ‖U row.1 u‖^2*‖V row.2 w‖^2) +
    (∑ col ∈ D, ‖V col.1 u‖^2*‖U col.2 w‖^2))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hh : H ⊆ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B :=
    (Finset.filter_subset _ _).trans hI
  have hmatrix (j b : ℕ) :
      ‖∑ row ∈ C, ∑ col ∈ D, if distanceMatrixIndex row col j b true ∈ H
        then F (distanceMatrixIndex row col j b true) else 0‖ ≤
        ‖graphRotatedDistanceWeight axis (angularBinCount θ) j b (u,w)‖ * S := by
    have he := distance_matrix_complex_bound_on I (a+n) j b θ axis true C D
      (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB)
      (sourceProductVertices_subset Q₂ Q₁ ν ρ B A a n hB hA)
      (fun row => U row.1 u*V row.2 w) (fun col => V col.1 u*U col.2 w)
      (graphRotatedDistanceWeight axis (angularBinCount θ) j b (u,w)) d (hdegree j b true)
    have hf (row col : CellPath × CellPath) : F (distanceMatrixIndex row col j b true) =
        graphRotatedDistanceWeight axis (angularBinCount θ) j b (u,w) *
          ((U row.1 u*V row.2 w)*conj (V col.1 u*U col.2 w)) := by
      dsimp [F,distanceMatrixIndex]
      rw [map_mul]
      ring
    simpa only [hf,norm_mul,mul_pow,H,S] using he
  change ‖∑ e ∈ H, F e‖ ≤ _
  rw [source_distance_graph_sum_occupied Q₁ Q₂ ρ ν A B N a n sig t hA hB H hh F,← hscale]
  calc
    _ ≤ ∑ j ∈ Finset.range (angularBinCount θ), ∑ b ∈ Finset.range (angularBinCount θ),
        ‖∑ row ∈ C, ∑ col ∈ D, if distanceMatrixIndex row col j b true ∈ H
          then F (distanceMatrixIndex row col j b true) else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ j ∈ Finset.range (angularBinCount θ), ∑ b ∈ Finset.range (angularBinCount θ),
        ‖graphRotatedDistanceWeight axis (angularBinCount θ) j b (u,w)‖*S :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun b _ => hmatrix j b))
    _ ≤ S := by
      simp only [← Finset.sum_mul]
      exact (mul_le_mul_of_nonneg_right
        (graphRotatedDistanceWeight_norm_total_le (angularBinCount_pos hθ) axis (u,w)) hS).trans_eq (one_mul S)
    _ = _ := by
      dsimp [S,C,D]
      rw [sourceProductVertices_swap_sum Q₁ Q₂ ρ ν A B n
        (fun c p => ‖V c u‖^2*‖U p w‖^2),Finset.sum_add_distrib]

end PlanarFalconer

end OAI
