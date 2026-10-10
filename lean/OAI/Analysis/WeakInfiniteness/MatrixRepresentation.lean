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

namespace WeakPureInfiniteness

section MatrixOperators

variable {n H : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def matrixOperator (M : CStarMatrix n n (H →L[ℂ] H)) :
    (PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H)) :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)
  e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i => ∑ j, (M i j).comp (ContinuousLinearMap.proj j)).comp
      e.toContinuousLinearMap)

omit [CompleteSpace H] in
@[simp]

lemma matrixOperator_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : n => H)) (i : n) :
    matrixOperator M x i = ∑ j, M i j (x j) := by
  simp [matrixOperator]

omit [CompleteSpace H] in
lemma matrixOperator_add (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M + N) = matrixOperator M + matrixOperator N := by
  ext x i
  simp [Finset.sum_add_distrib]

omit [CompleteSpace H] in
lemma matrixOperator_smul (c : ℂ) (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (c • M) = c • matrixOperator M := by
  ext x i
  simp [Finset.smul_sum]

omit [CompleteSpace H] in
lemma matrixOperator_zero : matrixOperator (0 : CStarMatrix n n (H →L[ℂ] H)) = 0 := by
  ext x i
  simp

omit [CompleteSpace H] in
lemma matrixOperator_mul (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M * N) = matrixOperator M * matrixOperator N := by
  ext x i
  simp only [matrixOperator_apply, CStarMatrix.mul_apply, sum_apply,
    mul_apply_eq_comp, map_sum]
  exact Finset.sum_comm

lemma matrixOperator_star (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (star M) = star (matrixOperator M) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, matrixOperator_apply, sum_inner, inner_sum,
    CStarMatrix.star_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

noncomputable def matrixOperatorHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    ((PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H))) where
  toFun := matrixOperator
  map_zero' := matrixOperator_zero
  map_add' := matrixOperator_add
  map_smul' := matrixOperator_smul
  map_mul' := matrixOperator_mul
  map_star' := matrixOperator_star

omit [CompleteSpace H] in
lemma matrixOperator_single [DecidableEq n] (M : CStarMatrix n n (H →L[ℂ] H)) (i j : n) (x : H) :
    matrixOperator M (PiLp.single 2 j x) i = M i j x := by
  simp [PiLp.single_apply, apply_ite]

omit [CompleteSpace H] in
lemma matrixOperator_injective : Function.Injective (matrixOperator (n := n) (H := H)) := by
  classical
  intro M N h
  ext i j x
  have he := congrArg (fun T => T (PiLp.single 2 j x) i) h
  simpa only [matrixOperator_single] using he

lemma norm_matrixOperator (M : CStarMatrix n n (H →L[ℂ] H)) :
    ‖matrixOperator M‖ = ‖M‖ := by
  exact NonUnitalStarAlgHom.norm_map (matrixOperatorHom (n := n) (H := H)) (by exact matrixOperator_injective (n := n) (H := H)) M

end MatrixOperators

end WeakPureInfiniteness
end

end OAI
