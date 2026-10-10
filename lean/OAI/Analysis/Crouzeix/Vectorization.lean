import Mathlib
import OAI.Analysis.Crouzeix.Amplification
import OAI.Analysis.Crouzeix.MatrixEndpoint
import OAI.Analysis.Crouzeix.RationalTransfer

namespace OAI

/-! Vectorization. -/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.L2Operator Kronecker InnerProductSpace MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Realization

def vectorization {n : ℕ} (X : Coeff n) : Amplification (EuclideanSpace ℂ (Fin n)) n :=
  ∑ j, ↑((Matrix.toEuclideanCLM (𝕜 := ℂ) X) (EuclideanSpace.basisFun (Fin n) ℂ j) ⊗ₜ[ℂ]
    (EuclideanSpace.basisFun (Fin n) ℂ j))

@[simp] theorem vectorization_coordinates {n : ℕ} (X : Coeff n) :
    matrixAmplificationCoordinates n n (vectorization X) = Boundary.toHS X := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  simp only [vectorization, map_sum, WithLp.ofLp_sum, Finset.sum_apply, matrixAmplificationCoordinates_tmul,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]
  simp [Boundary.toHS]

@[simp] theorem norm_vectorization {n : ℕ} (X : Coeff n) :
    ‖vectorization X‖ = ‖Boundary.toHS X‖ := by
  rw [← norm_matrixAmplificationCoordinates n n, vectorization_coordinates]

theorem kronecker_toHS {n : ℕ} (A B X : Coeff n) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ B)) (Boundary.toHS X) =
      Boundary.toHS (A * X * Bᵀ) := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Boundary.toHS,
    WithLp.ofLp_toLp, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorOperator_vectorization {n : ℕ} (A B X : Coeff n) :
    tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) A) B (vectorization X) =
      vectorization (A * X * Bᵀ) := by
  let e : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  apply e.injective
  change matrixAmplificationCoordinates n n _ = matrixAmplificationCoordinates n n _
  rw [matrixAmplificationCoordinates_tensorOperator, vectorization_coordinates,
    vectorization_coordinates, kronecker_toHS]

namespace Endpoint

open Boundary

theorem EndpointFactors.exists_colligation {n : ℕ} {T H : Coeff n} {κ : ℝ}
    (E : EndpointFactors T κ H) :
    ∃ C : Realization.Colligation (EuclideanSpace ℂ (Fin n)),
      CFC.sqrt E.Q =
        (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)) * CFC.sqrt E.Q *
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a +
            E.X * (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.c ∧
      E.Y = (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)) * CFC.sqrt E.Q *
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.b +
          E.X * (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.d := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  let D := CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)
  let L := CFC.sqrt E.Q
  have hL : L * Lᴴ = E.Q := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg E.Q)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self E.Q E.Q_positive.nonneg
  have hbal : L * Lᴴ + E.Y * E.Yᴴ = (D * L) * (D * L)ᴴ + E.X * E.Xᴴ := by
    rw [Matrix.conjTranspose_mul]
    have he : (D * L) * (Lᴴ * Dᴴ) = D * E.Q * Dᴴ := by
      rw [mul_assoc D L, ← mul_assoc L, hL, ← mul_assoc]
    rw [he, hL]
    have h := E.balance
    change E.X * E.Xᴴ - E.Y * E.Yᴴ = E.Q - D * E.Q * Dᴴ at h
    apply sub_eq_sub_iff_add_eq_add.mp at h
    rw [add_comm] at h
    exact h.symm
  obtain ⟨C, hC, hY⟩ := Realization.exists_colligation_data (e D) (e L) (e E.X) (e E.Y)
    (by simpa only [← map_mul, ← map_star, ← map_add, Matrix.star_eq_conjTranspose]
        using congrArg e hbal)
  refine ⟨C, ?_, ?_⟩
  · simpa only [map_add, map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm hC
  · simpa only [map_add, map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm hY

end Endpoint

end CrouzeixHilbert

end

end OAI
