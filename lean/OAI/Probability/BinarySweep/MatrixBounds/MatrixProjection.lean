import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

def projectionMatrix (S : Submodule ℂ (EuclideanSpace ℂ I)) : Matrix I I ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm S.starProjection

lemma projectionMatrix_linear (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    (projectionMatrix S).toEuclideanLin = S.starProjection.toLinearMap := by
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply S.starProjection
  exact congrArg ContinuousLinearMap.toLinearMap h

lemma projectionMatrix_psd (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    (projectionMatrix S).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, projectionMatrix_linear]
  exact (Submodule.isSymmetricProjection_starProjection S).isPositive

lemma projectionMatrix_idempotent (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    projectionMatrix S * projectionMatrix S = projectionMatrix S := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ)).injective
  simp only [map_mul]
  have h : (Matrix.toEuclideanCLM (𝕜 := ℂ)).toRingEquiv (projectionMatrix S) =
      S.starProjection := (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply _
  rw [h]
  exact S.isIdempotentElem_starProjection

lemma trace_toEuclideanLinear (M : Matrix I I ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ I) M.toEuclideanLin = M.trace := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun I ℂ)]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  simp [EuclideanSpace.basisFun_apply, PiLp.inner_apply, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, PiLp.ofLp_single, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma projectionMatrix_trace (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    (projectionMatrix S).trace = (Module.finrank ℂ S : ℂ) := by
  rw [← trace_toEuclideanLinear, projectionMatrix_linear]
  have h : LinearMap.IsProj S S.starProjection.toLinearMap :=
    ⟨S.starProjection_apply_mem, fun v hv => Submodule.starProjection_eq_self_iff.mpr hv⟩
  exact h.trace

lemma projectionMatrix_coeff (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    LinearMap.toMatrix' ((WithLp.linearEquiv 2 ℂ (I → ℂ)).conj S.starProjection.toLinearMap) =
      projectionMatrix S := by
  apply Matrix.toEuclideanLin.injective
  rw [projectionMatrix_linear]
  ext v i
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin, LinearEquiv.conj_apply]
  simp

omit [DecidableEq I] in
lemma projectionMatrix_commutes (S : Submodule ℂ (EuclideanSpace ℂ I))
    (f : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ I) (hf : S.map f.toLinearMap = S)
    (v : EuclideanSpace ℂ I) :
    f (S.starProjection v) = S.starProjection (f v) := by
  have h := f.map_starProjection S v
  simpa only [hf] using h

end BinaryCoordinateSweeps.Density

end

end OAI
