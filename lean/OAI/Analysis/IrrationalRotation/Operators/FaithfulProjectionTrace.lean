import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Rotation.ProjectionDiagonalPropagation

namespace OAI

noncomputable section
open scoped InnerProductSpace

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem strict_positive_trace_of_nonzero_projection
    (M : VonNeumannAlgebra H) (ξ : H) (htrace : IsFaithfulTracialVector M ξ)
    (P : H →L[ℂ] H) (hPm : P ∈ M) (hP : IsStarProjection P) (hP0 : P ≠ 0) :
    0 < (vectorTrace ξ P).re := by
  have hnonneg := (InvariantProjection.projection_re_inner_bounds hP ξ).1
  apply lt_of_le_of_ne hnonneg
  intro heq
  have hzero : P ξ = 0 :=
    (InvariantProjection.projection_re_inner_eq_zero_iff hP ξ).mp heq.symm
  apply hP0
  exact htrace.2.2 P hPm (ContinuousLinearMap.IsPositive.of_isStarProjection hP)
    (by simp only [vectorTrace, hzero, inner_zero_right])

theorem strict_trace_bounds_of_nontrivial_projection
    (M : VonNeumannAlgebra H) (ξ : H) (htrace : IsFaithfulTracialVector M ξ)
    (P : H →L[ℂ] H) (hPm : P ∈ M) (hP : IsStarProjection P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    0 < (vectorTrace ξ P).re ∧ (vectorTrace ξ P).re < 1 := by
  refine ⟨strict_positive_trace_of_nonzero_projection M ξ htrace P hPm hP hP0, ?_⟩
  have hcomp := strict_positive_trace_of_nonzero_projection M ξ htrace
    (1 - P) (M.sub_mem M.one_mem hPm) hP.one_sub
    (sub_ne_zero.mpr (Ne.symm hP1))
  have hself : (inner ℂ ξ ξ).re = 1 := by
    calc
      (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) ξ
      _ = 1 := by rw [htrace.1]; norm_num
  simp only [vectorTrace, sub_apply,
    one_apply_eq_self, inner_sub_right, Complex.sub_re,
    hself] at hcomp ⊢
  exact sub_pos.mp hcomp

end Invariant233

end

end OAI
