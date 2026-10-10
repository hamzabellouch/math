import OAI.Geometry.ProjectionVolume.FacetAreas
import OAI.Geometry.ProjectionVolume.SimplexNormals
import OAI.Geometry.ProjectionVolume.ProjectionJacobian

namespace OAI

open Set
open scoped RealInnerProductSpace

namespace Paper092

def coordinateDrop (n : ℕ) (i : Fin (n + 1)) : Euclidean (n + 1) →ₗ[ℝ] Euclidean n where
  toFun y := WithLp.toLp 2 (i.removeNth y)
  map_add' x y := by ext j; rfl
  map_smul' a x := by ext j; rfl

theorem coordinateDrop_apply (n : ℕ) (i : Fin (n + 1)) (y : Euclidean (n + 1)) (j : Fin n) :
    coordinateDrop n i y j = y (i.succAbove j) := rfl

theorem coordinateDrop_facetEmbedding (n : ℕ) (i : Fin (n + 1)) (c : ℝ) (x : Euclidean n) :
    coordinateDrop n i (facetEmbedding n i c x) = x := by
  ext j
  exact facetEmbedding_apply_succAbove n i c x j

theorem facetEmbedding_mem_diagonal_tangent (n : ℕ) (i : Fin (n + 1)) (x : Euclidean n) :
    facetEmbedding n i (-1) x ∈ normalHyperplane (diagonalVector (n + 1)) := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  rw [diagonalVector_inner, Fin.sum_univ_succAbove _ i]
  simp only [facetEmbedding_apply_same, facetEmbedding_apply_succAbove, neg_one_mul, neg_add_cancel]

noncomputable def diagonalTangentEmbedding (n : ℕ) (i : Fin (n + 1)) :
    Euclidean n →ₗ[ℝ] normalHyperplane (diagonalVector (n + 1)) :=
  (facetEmbedding n i (-1)).codRestrict _ (facetEmbedding_mem_diagonal_tangent n i)

noncomputable def diagonalCoordinateDrop (n : ℕ) (i : Fin (n + 1)) :
    normalHyperplane (diagonalVector (n + 1)) →ₗ[ℝ] Euclidean n :=
  (coordinateDrop n i).comp (normalHyperplane (diagonalVector (n + 1))).subtype

theorem diagonalCoordinateDrop_comp_embedding (n : ℕ) (i : Fin (n + 1)) :
    (diagonalCoordinateDrop n i).comp (diagonalTangentEmbedding n i) = LinearMap.id := by
  ext x j
  exact congrArg (fun y : Euclidean n => y j) (coordinateDrop_facetEmbedding n i (-1) x)

theorem diagonalCoordinateDrop_normDet (n : ℕ) (i : Fin (n + 1)) :
    (diagonalCoordinateDrop n i).normDet = 1 / Real.sqrt (n + 1) := by
  have hn : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hw : diagonalVector (n + 1) ≠ 0 := by
    intro h
    have hh := diagonalVector_norm (n + 1)
    simp only [h, norm_zero, Nat.cast_add, Nat.cast_one] at hh
    exact hn.ne' hh.symm
  have hdim : Module.finrank ℝ (Euclidean n) =
      Module.finrank ℝ (normalHyperplane (diagonalVector (n + 1))) := by
    rw [finrank_euclideanSpace_fin, normalHyperplane_finrank _ hw, Nat.add_sub_cancel]
  have h := LinearMap.normDet_comp_of_finrank_eq
    (diagonalTangentEmbedding n i) (diagonalCoordinateDrop n i) hdim
  rw [diagonalCoordinateDrop_comp_embedding] at h
  have he : (diagonalTangentEmbedding n i).normDet = Real.sqrt (n + 1) := by
    rw [diagonalTangentEmbedding, LinearMap.normDet_codRestrict, facetEmbedding_normDet_neg_one]
  rw [he] at h
  have hh : 1 = (diagonalCoordinateDrop n i).normDet * Real.sqrt (n + 1) := by simpa using h
  exact (eq_div_iff hn.ne').mpr hh.symm

theorem coordinateDrop_diagonalFacet (n : ℕ) (i : Fin (n + 1)) :
    coordinateDrop n i '' simplexFacet (n + 1) none = standardSimplex n := by
  rw [← diagonalFacetChart_image n i, image_image]
  have he : (fun x => coordinateDrop n i (diagonalFacetChart n i x)) = id := by
    funext x
    ext j
    simp [coordinateDrop, diagonalFacetChart]
  rw [he, image_id]

end Paper092

end OAI
