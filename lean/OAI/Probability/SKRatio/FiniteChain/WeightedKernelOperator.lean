import Mathlib
import OAI.Probability.SKRatio.Matrices.WeightedSquares
import OAI.Probability.SKRatio.Matrices.CompactMatrixMasks

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet

theorem weighted_square_operator_rare {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (β : ℝ) (G : X × X → ℝ) (hG : Continuous G) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (law β) (fun n => {g | ∃ x : Fin n → X,
      u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (Matrix.of fun i j => squareError β g i j*G (x i,x j))‖}) := by
  obtain ⟨C,hC,hrow⟩ := square_rows_bounded β
  obtain ⟨δ,hδ,hmask⟩ := continuous_kernel_insertion G hG
    (show 0≤C+β^2 by positivity) hu
  apply (hrow.union (squareError_rare β hδ)).mono
  refine Filter.Eventually.of_forall ?_
  rintro n g ⟨x,hx⟩
  by_contra hn
  have hr : ∀ i, ∑ j, |squareError β g i j| ≤ C+β^2 := by
    intro i
    exact (squareError_absolute_row β g i).trans (add_le_add_left
      (le_of_not_gt (fun hi => hn (Or.inl ⟨i,hi⟩))) _)
  have hc : ∀ j, ∑ i, |squareError β g i j| ≤ C+β^2 := by
    intro j
    simpa only [squareError_symmetric β g] using hr j
  have hd : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (squareError β g)‖ ≤ δ :=
    le_of_not_gt (fun h => hn (Or.inr h))
  exact (not_lt_of_ge (hmask (squareError β g) hr hc hd x)) hx

end SKRatio.Planted

end
end

end OAI
