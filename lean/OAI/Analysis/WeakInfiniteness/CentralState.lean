import Mathlib
import OAI.Analysis.WeakInfiniteness.MatrixTensorExact

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace ENNReal MatrixOrder

universe u v

section VectorState

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorStateLinear (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : A →ₗ[ℂ] ℂ where
  toFun a := inner ℂ ξ (π a ξ)
  map_add' a b := by simp
  map_smul' c a := by simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma vectorStateLinear_bound (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    ‖vectorStateLinear π ξ a‖≤‖ξ‖^2*‖a‖ := by
  calc
    _ ≤ ‖ξ‖*‖π a ξ‖ := norm_inner_le_norm ξ _
    _ ≤ ‖ξ‖*(‖π a‖*‖ξ‖) := mul_le_mul_of_nonneg_left ((π a).le_opNorm ξ) (norm_nonneg _)
    _ ≤ ‖ξ‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le _ _
    _ = _ := by ring

def vectorStateContinuous (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : A →L[ℂ] ℂ :=
  (vectorStateLinear π ξ).mkContinuous (‖ξ‖^2) (vectorStateLinear_bound π ξ)

omit [PartialOrder A] [StarOrderedRing A] in
lemma vectorStateContinuous_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    vectorStateContinuous π ξ a=inner ℂ ξ (π a ξ) := rfl

lemma vectorStateContinuous_cp (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    CompletelyPositive (vectorStateContinuous π ξ) := by
  classical
  intro n x hx
  let : Module ℝ (CStarMatrix (Fin n) (Fin n) A) := Module.complexToReal _
  let y := CFC.sqrt x
  have hy : star y*y=x := by
    dsimp only [y]
    rw [(CFC.sqrt_nonneg x).star_eq,CFC.sqrt_mul_sqrt_self x hx]
  have he : CStarMatrix.ofMatrix (fun i j => vectorStateContinuous π ξ (x i j))=
      ∑ k : Fin n,CStarMatrix.ofMatrix (Matrix.gram ℂ (fun i => π (y k i) ξ)) := by
    ext i j
    rw [← hy]
    simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply,vectorStateContinuous_apply,
      map_sum,map_mul,map_star,mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    change (∑ k,inner ℂ (π (y k i) ξ) (π (y k j) ξ)) =
      matrixEntryLinear i j (∑ k : Fin n,CStarMatrix.ofMatrix (Matrix.gram ℂ (fun i => π (y k i) ξ)))
    rw [map_sum]
    rfl
  rw [he]
  apply Finset.sum_nonneg
  intro k _
  exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (Matrix.posSemidef_gram ℂ _).nonneg

omit [PartialOrder A] [StarOrderedRing A] in
lemma vectorStateContinuous_norm_le (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    ‖vectorStateContinuous π ξ‖≤‖ξ‖^2 :=
  ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _) (vectorStateLinear_bound π ξ)

end VectorState

end

end WeakPureInfiniteness
end

end OAI
