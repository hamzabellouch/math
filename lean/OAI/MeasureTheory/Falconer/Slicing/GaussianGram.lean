import OAI.MeasureTheory.Falconer.Slicing.GaussianMultiband
import Mathlib.Analysis.InnerProductSpace.NormDet

namespace OAI

/-! # Coordinate-free determinant in the Gaussian multi-band bound -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d j : ℕ}

theorem bandCoordinateMap_adjoint_basis (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (hw : ∀ i, w i ∈ V) (b : V ≃ₗᵢ[ℝ] Space j) (i : Fin j) :
    (bandCoordinateMap w V b).adjoint (EuclideanSpace.basisFun (Fin j) ℝ i) = b ⟨w i,hw i⟩ := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left,EuclideanSpace.basisFun_inner,
    bandCoordinateMap_apply]
  have hi := b.inner_map_map ⟨w i,hw i⟩ (b.symm x)
  simpa only [b.apply_symm_apply,Submodule.coe_inner] using hi.symm

theorem bandCoordinateMap_det_sq (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (hw : ∀ i, w i ∈ V) (b : V ≃ₗᵢ[ℝ] Space j) :
    (LinearMap.det (bandCoordinateMap w V b : Space j →ₗ[ℝ] Space j))^2 =
      (Matrix.gram ℝ w).det := by
  let L := bandCoordinateMap w V b
  have hh := L.adjoint.toLinearMap.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin j) ℝ)
  change (L.adjoint.toLinearMap.normDet : ℝ)^2 =
    (Matrix.gram ℝ (fun i => L.adjoint (EuclideanSpace.basisFun (Fin j) ℝ i))).det at hh
  have he : Matrix.gram ℝ (fun i => L.adjoint (EuclideanSpace.basisFun (Fin j) ℝ i)) =
      Matrix.gram ℝ w := by
    ext i k
    simp only [Matrix.gram_apply,L,bandCoordinateMap_adjoint_basis w V hw b,
      b.inner_map_map]
    rfl
  rw [he,LinearMap.normDet_eq_norm_det] at hh
  have hd : LinearMap.det L.adjoint.toLinearMap = LinearMap.det L.toLinearMap := by
    rw [← ContinuousLinearMap.adjoint_toLinearMap,
      ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin j) ℝ).toBasis,
      LinearMap.toMatrix_adjoint,Matrix.det_conjTranspose]
    simp only [star_trivial,LinearMap.det_toMatrix]
  rw [hd] at hh
  simpa only [Real.norm_eq_abs,sq_abs] using hh

end Falconer

end OAI
