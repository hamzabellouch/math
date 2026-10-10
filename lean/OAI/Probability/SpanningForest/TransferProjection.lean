import Mathlib

namespace OAI

noncomputable section

namespace Problem336
namespace TransferProjection

section Abstract

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem adjoint_rightInverse_projection
    (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] F)
    (hB : (A ∘ₗ A.adjoint) ∘ₗ B = LinearMap.id) (x : E) :
    A.kerᗮ.starProjection x = A.adjoint (B (A x)) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [A.orthogonal_ker]
    exact ⟨B (A x), rfl⟩
  · rw [Submodule.orthogonal_orthogonal]
    change A (x - A.adjoint (B (A x))) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun hB (A x)
    change A (A.adjoint (B (A x))) = A x at h
    rw [h, sub_self]

theorem adjoint_rightInverse_eq_complement
    (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] F)
    (hB : (A ∘ₗ A.adjoint) ∘ₗ B = LinearMap.id) (x : E) :
    A.adjoint (B (A x)) = x - A.ker.starProjection x := by
  rw [← adjoint_rightInverse_projection A B hB x]
  exact A.ker.starProjection_orthogonal_val x

end Abstract

section Embedding

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem map_projection_adjoint (j : E →ₗᵢ[ℝ] H) (C : Submodule ℝ E) (x : H) :
    (C.map j.toLinearMap).starProjection x =
      j (C.starProjection (j.toContinuousLinearMap.adjoint x)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨C.starProjection (j.toContinuousLinearMap.adjoint x),
      C.starProjection_apply_mem _, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [inner_sub_left]
    change inner ℝ x (j y) -
      inner ℝ (j (C.starProjection (j.toContinuousLinearMap.adjoint x))) (j y) = 0
    have ha : inner ℝ x (j y) = inner ℝ (j.toContinuousLinearMap.adjoint x) y :=
      (j.toContinuousLinearMap.adjoint_inner_left y x).symm
    rw [j.inner_map_map, ha, ← inner_sub_left]
    exact C.starProjection_inner_eq_zero _ y hy

theorem range_projection_adjoint (j : E →ₗᵢ[ℝ] H) (x : H) :
    j.toLinearMap.range.starProjection x = j (j.toContinuousLinearMap.adjoint x) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  simpa [Submodule.starProjection_top] using
    map_projection_adjoint j (⊤ : Submodule ℝ E) x

theorem embedded_complement_projection (j : E →ₗᵢ[ℝ] H)
    (C : Submodule ℝ E) (x : H) :
    j (j.toContinuousLinearMap.adjoint x -
      C.starProjection (j.toContinuousLinearMap.adjoint x)) =
      j.toLinearMap.range.starProjection x - (C.map j.toLinearMap).starProjection x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [map_sub, range_projection_adjoint, map_projection_adjoint]

end Embedding

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def transferMatrix (A : Matrix m n ℝ) : Matrix n n ℝ :=
  A.transpose * (A * A.transpose)⁻¹ * A

theorem transferMatrix_eq_complement (A : Matrix m n ℝ)
    (hA : IsUnit (A * A.transpose).det) (x : EuclideanSpace ℝ n) :
    (transferMatrix A).toEuclideanLin x =
      x - A.toEuclideanLin.ker.starProjection x := by
  have hadj : A.transpose.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using A.toEuclideanLin_conjTranspose_eq_adjoint
  have hright :
      (A.toEuclideanLin ∘ₗ A.toEuclideanLin.adjoint) ∘ₗ
        (A * A.transpose)⁻¹.toEuclideanLin = LinearMap.id := by
    rw [← hadj, ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
    rw [Matrix.mul_nonsing_inv _ hA, Matrix.toLpLin_one]
  have h := adjoint_rightInverse_eq_complement A.toEuclideanLin
    (A * A.transpose)⁻¹.toEuclideanLin hright x
  simpa only [transferMatrix, Matrix.toLpLin_mul_same, LinearMap.comp_apply, hadj] using h

theorem embedded_transferMatrix_eq_difference
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Matrix m n ℝ) (hA : IsUnit (A * A.transpose).det)
    (j : EuclideanSpace ℝ n →ₗᵢ[ℝ] H) (x : H) :
    j ((transferMatrix A).toEuclideanLin (j.toContinuousLinearMap.adjoint x)) =
      j.toLinearMap.range.starProjection x -
        (A.toEuclideanLin.ker.map j.toLinearMap).starProjection x := by
  rw [transferMatrix_eq_complement A hA]
  exact embedded_complement_projection j A.toEuclideanLin.ker x

theorem transferMatrix_entry_eq_inner (A : Matrix m n ℝ)
    (hA : IsUnit (A * A.transpose).det) (i k : n) :
    transferMatrix A i k = inner ℝ (EuclideanSpace.basisFun n ℝ i)
      (EuclideanSpace.basisFun n ℝ k -
        A.toEuclideanLin.ker.starProjection (EuclideanSpace.basisFun n ℝ k)) := by
  rw [← transferMatrix_eq_complement A hA, EuclideanSpace.basisFun_inner]
  simp [Matrix.toLpLin_apply]

end TransferProjection
end Problem336

end

end OAI
