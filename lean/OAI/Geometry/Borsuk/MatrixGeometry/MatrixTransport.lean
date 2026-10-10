import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.Rank

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

noncomputable def matrixConjugate (e : E ≃ₗᵢ[ℝ] E) : M ≃⋆ₐ[ℝ] M :=
  (op).trans (e.conjStarAlgEquiv.trans (op).symm)

lemma matrixConjugate_action (e : E ≃ₗᵢ[ℝ] E) (A : M) (v : E) :
    op (matrixConjugate e A) v = e (op A (e.symm v)) := by
  simp only [matrixConjugate,StarAlgEquiv.trans_apply,StarAlgEquiv.apply_symm_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

lemma matrixConjugate_nonneg (e : E ≃ₗᵢ[ℝ] E) {A : M} (hA : 0 ≤ A) :
    0 ≤ matrixConjugate e A := map_nonneg _ hA

lemma matrixConjugate_rankOne (e : E ≃ₗᵢ[ℝ] E) (u : E) :
    matrixConjugate e (rankOne u) = rankOne (e u) := by
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (matrixConjugate e (rankOne u)) = op (rankOne (e u))
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action,rankOne_action,rankOne_action,map_smul]
  congr 1
  simpa using (e.inner_map_map u (e.symm v)).symm

lemma matrix_operator_trace (A : M) : LinearMap.trace ℝ E (op A).toLinearMap = Matrix.trace A := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq A _

lemma matrixConjugate_trace (e : E ≃ₗᵢ[ℝ] E) (A : M) :
    Matrix.trace (matrixConjugate e A) = Matrix.trace A := by
  rw [← matrix_operator_trace,← matrix_operator_trace]
  have he : (op (matrixConjugate e A)).toLinearMap = e.toLinearEquiv.conj (op A).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact matrixConjugate_action e A v
  rw [he,LinearMap.trace_conj']

lemma matrixConjugate_kernel (e : E ≃ₗᵢ[ℝ] E) {A : M} {v : E} (hv : op A v = 0) :
    op (matrixConjugate e A) (e v) = 0 := by
  rw [matrixConjugate_action,e.symm_apply_apply,hv,map_zero]

lemma matrixConjugate_range (e : E ≃ₗᵢ[ℝ] E) {A : M} {v : E}
    (hv : v ∈ LinearMap.range (op A).toLinearMap) :
    e v ∈ LinearMap.range (op (matrixConjugate e A)).toLinearMap := by
  obtain ⟨x,rfl⟩ := hv
  exact ⟨e x,by simp only [ContinuousLinearMap.coe_coe,matrixConjugate_action,e.symm_apply_apply]⟩

lemma matrixConjugate_selfAdjoint (e : E ≃ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (matrixConjugate e A) := by
  rw [IsSelfAdjoint,← map_star,hA.star_eq]

lemma matrixConjugate_involutive {e : E ≃ₗᵢ[ℝ] E}
    (he : ∀ v, e (e v) = v) (A : M) : matrixConjugate e (matrixConjugate e A) = A := by
  have hes : ∀ v, e.symm v = e v := by intro v; apply e.injective; simp [he]
  apply (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).injective
  change op (matrixConjugate e (matrixConjugate e A)) = op A
  apply ContinuousLinearMap.ext
  intro v
  simp only [matrixConjugate_action,hes,he]

end MatrixTransport
end BorsukNine

end OAI
