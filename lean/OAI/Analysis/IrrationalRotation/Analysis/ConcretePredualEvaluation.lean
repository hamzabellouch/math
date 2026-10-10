import OAI.Analysis.IrrationalRotation.Analysis.ConcretePredualCore
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance evaluationPredualNormedAddCommGroup (M : VonNeumannAlgebra H) : NormedAddCommGroup (predual M) :=
  (predual M).normedAddCommGroup
local instance evaluationPredualNormedSpace (M : VonNeumannAlgebra H) : NormedSpace ℂ (predual M) :=
  (predual M).normedSpace

private theorem vector_norm_bound (M : VonNeumannAlgebra H) (x y : H) :
    ‖vector M x y‖ ≤ ‖x‖ * ‖y‖ := by
  change ‖vectorFunctional M x y‖ ≤ ‖x‖ * ‖y‖
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro A
  change ‖inner ℂ x ((A : H →L[ℂ] H) y)‖ ≤ (‖x‖ * ‖y‖) * ‖A‖
  calc
    ‖inner ℂ x ((A : H →L[ℂ] H) y)‖ ≤ ‖x‖ * ‖(A : H →L[ℂ] H) y‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖(A : H →L[ℂ] H)‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((A : H →L[ℂ] H).le_opNorm y) (norm_nonneg _)
    _ = (‖x‖ * ‖y‖) * ‖A‖ := by change _ = (‖x‖ * ‖y‖) * ‖(A : H →L[ℂ] H)‖; ring

theorem norm_evaluation_le (M : VonNeumannAlgebra H) (A : M) :
    ‖evaluation M A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  calc
    ‖evaluation M A f‖ ≤ ‖(f : StrongDual ℂ M)‖ * ‖A‖ :=
      (f : StrongDual ℂ M).le_opNorm A
    _ = ‖A‖ * ‖f‖ := mul_comm _ _

theorem norm_le_evaluation (M : VonNeumannAlgebra H) (A : M) :
    ‖A‖ ≤ ‖evaluation M A‖ := by
  change ‖(A : H →L[ℂ] H)‖ ≤ ‖evaluation M A‖
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg _)
  intro x y hx hy
  calc
    (inner ℂ ((A : H →L[ℂ] H) x) y).re =
        (inner ℂ y ((A : H →L[ℂ] H) x)).re := inner_re_symm (𝕜 := ℂ) _ _
    _ ≤ ‖inner ℂ y ((A : H →L[ℂ] H) x)‖ := Complex.re_le_norm _
    _ = ‖evaluation M A (vector M y x)‖ := rfl
    _ ≤ ‖evaluation M A‖ * ‖vector M y x‖ :=
      (evaluation M A).le_opNorm _
    _ ≤ ‖evaluation M A‖ * (‖y‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (vector_norm_bound M y x) (norm_nonneg _)
    _ = ‖evaluation M A‖ := by rw [hy, hx]; ring

@[simp] theorem norm_evaluation (M : VonNeumannAlgebra H) (A : M) :
    ‖evaluation M A‖ = ‖A‖ :=
  le_antisymm (norm_evaluation_le M A) (norm_le_evaluation M A)

def evaluationLinearIsometry (M : VonNeumannAlgebra H) :
    M →ₗᵢ[ℂ] StrongDual ℂ (predual M) where
  toFun := evaluation M
  map_add' A B := by
    ext f
    exact (f : StrongDual ℂ M).map_add A B
  map_smul' c A := by
    ext f
    exact (f : StrongDual ℂ M).map_smul c A
  norm_map' := norm_evaluation M

@[simp] theorem evaluationLinearIsometry_apply (M : VonNeumannAlgebra H) (A : M) :
    evaluationLinearIsometry M A = evaluation M A := rfl

theorem evaluation_injective (M : VonNeumannAlgebra H) :
    Function.Injective (evaluation M) :=
  (evaluationLinearIsometry M).injective

end Invariant233.ConcretePredual

end

end OAI
