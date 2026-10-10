import Mathlib

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

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

abbrev HilbertVector (n H : Type*) [NormedAddCommGroup H] := PiLp 2 (fun _ : n => H)

def matrixAction (M : CStarMatrix m n (H →L[ℂ] H)) :
    HilbertVector n H →L[ℂ] HilbertVector m H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : m => H)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i => ∑ j, (M i j).comp (ContinuousLinearMap.proj j)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)).toContinuousLinearMap)

omit [CompleteSpace H] [Fintype m] in
@[simp]

lemma matrixAction_apply (M : CStarMatrix m n (H →L[ℂ] H))
    (x : HilbertVector n H) (i : m) : matrixAction M x i = ∑ j, M i j (x j) := by
  simp [matrixAction]

omit [CompleteSpace H] in
lemma matrixAction_add (M N : CStarMatrix m n (H →L[ℂ] H)) :
    matrixAction (M+N)=matrixAction M+matrixAction N := by
  ext x i
  simp [matrixAction_apply, Finset.sum_add_distrib]

omit [CompleteSpace H] in
lemma matrixAction_smul (c : ℂ) (M : CStarMatrix m n (H →L[ℂ] H)) :
    matrixAction (c • M)=c • matrixAction M := by
  ext x i
  simp [matrixAction_apply, Finset.smul_sum]

omit [CompleteSpace H] [Fintype m] in
lemma matrixAction_mul (M : CStarMatrix m n (H →L[ℂ] H))
    (N : CStarMatrix n k (H →L[ℂ] H)) :
    matrixAction (M*N)=(matrixAction M).comp (matrixAction N) := by
  ext x i
  simp only [matrixAction_apply, CStarMatrix.mul_apply, sum_apply,
    mul_apply_eq_comp, ContinuousLinearMap.comp_apply, map_sum]
  rw [Finset.sum_comm]

lemma matrixAction_star (M : CStarMatrix m n (H →L[ℂ] H)) :
    matrixAction M.conjTranspose=(matrixAction M).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, matrixAction_apply, CStarMatrix.conjTranspose_apply,
    sum_inner, inner_sum, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  rw [Finset.sum_comm]

def matrixActionHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    (HilbertVector n H →L[ℂ] HilbertVector n H) where
  toFun := matrixAction
  map_zero' := by ext x i; simp
  map_add' := matrixAction_add
  map_smul' := matrixAction_smul
  map_mul' := matrixAction_mul
  map_star' := matrixAction_star

variable {A : Type*} [NonUnitalCStarAlgebra A]

def matrixRepresentation (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (n : Type*) [Fintype n] :
    CStarMatrix n n A →⋆ₙₐ[ℂ] (HilbertVector n H →L[ℂ] HilbertVector n H) :=
  matrixActionHom.comp (CStarMatrix.mapₙₐ π)

@[simp]
lemma matrixRepresentation_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : CStarMatrix n n A) (x : HilbertVector n H) (i : n) :
    matrixRepresentation π n M x i = ∑ j, π (M i j) (x j) := by
  change matrixAction ((CStarMatrix.mapₙₐ π) M) x i = _
  rw [matrixAction_apply]
  rfl

end

end WeakPureInfiniteness
end

end OAI
