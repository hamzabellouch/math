import OAI.Geometry.ProjectionVolume.ProductVolume
import OAI.Geometry.ProjectionVolume.SimplexProjection
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace Paper092

def facetEmbedding (n : ℕ) (i : Fin (n + 1)) (c : ℝ) :
    Euclidean n →ₗ[ℝ] Euclidean (n + 1) where
  toFun x := WithLp.toLp 2 (i.insertNth (c * ∑ j, x j) x)
  map_add' x y := by
    ext j
    induction j using i.succAboveCases <;>
      simp [PiLp.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' a x := by
    ext j
    induction j using i.succAboveCases <;>
      simp [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem facetEmbedding_apply_same (n : ℕ) (i : Fin (n + 1)) (c : ℝ) (x : Euclidean n) :
    facetEmbedding n i c x i = c * ∑ j, x j := by
  simp [facetEmbedding]

theorem facetEmbedding_apply_succAbove (n : ℕ) (i : Fin (n + 1)) (c : ℝ)
    (x : Euclidean n) (j : Fin n) :
    facetEmbedding n i c x (i.succAbove j) = x j := by
  simp [facetEmbedding]

theorem facetEmbedding_inner (n : ℕ) (i : Fin (n + 1)) (c : ℝ) (x y : Euclidean n) :
    ⟪facetEmbedding n i c x, facetEmbedding n i c y⟫ =
      ⟪x, y⟫ + c ^ 2 * (∑ j, x j) * (∑ j, y j) := by
  rw [PiLp.inner_apply, Fin.sum_univ_succAbove _ i]
  simp only [facetEmbedding_apply_same, facetEmbedding_apply_succAbove, Real.inner_apply,
    PiLp.inner_apply]
  ring

theorem facetEmbedding_normDet_sq (n : ℕ) (i : Fin (n + 1)) (c : ℝ) :
    (facetEmbedding n i c).normDet ^ 2 = 1 + (n : ℝ) * c ^ 2 := by
  have hsq := (facetEmbedding n i c).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hsq
  have hgram : Matrix.gram ℝ
      (fun j => facetEmbedding n i c (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      1 + Matrix.replicateCol (Fin 1) (fun _ : Fin n => c) *
        Matrix.replicateRow (Fin 1) (fun _ : Fin n => c) := by
    ext j k
    simp only [Matrix.gram_apply, facetEmbedding_inner,
      (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite]
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, Matrix.one_apply,
      Matrix.mul_apply, pow_two]
  rw [hgram] at hsq
  have hd := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (fun _ : Fin n => c) (fun _ : Fin n => c)
  simpa [dotProduct, pow_two, mul_assoc] using hsq.trans hd

theorem facetEmbedding_normDet_zero (n : ℕ) (i : Fin (n + 1)) :
    (facetEmbedding n i 0).normDet = 1 := by
  have h := facetEmbedding_normDet_sq n i 0
  have hp := (facetEmbedding n i 0).normDet_nonneg
  nlinarith

theorem facetEmbedding_normDet_neg_one (n : ℕ) (i : Fin (n + 1)) :
    (facetEmbedding n i (-1)).normDet = Real.sqrt (n + 1) := by
  have h := facetEmbedding_normDet_sq n i (-1)
  have hp := (facetEmbedding n i (-1)).normDet_nonneg
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  have hsp := Real.sqrt_nonneg ((n : ℝ) + 1)
  nlinarith

theorem facetEmbedding_zero_image (n : ℕ) (i : Fin (n + 1)) :
    facetEmbedding n i 0 '' standardSimplex n = simplexFacet (n + 1) (some i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change facetEmbedding n i 0 x ∈ standardSimplex (n + 1) ∧
      facetEmbedding n i 0 x i = 0
    rw [mem_standardSimplex_iff] at hx ⊢
    simp [facetEmbedding, Fin.forall_iff_succAbove i, hx]
  · rintro ⟨hy, hi⟩
    change y i = 0 at hi
    refine ⟨WithLp.toLp 2 (i.removeNth y), ?_, ?_⟩
    · rw [mem_standardSimplex_iff] at hy ⊢
      refine ⟨fun j => hy.1 (i.succAbove j), ?_⟩
      have hsum := Fin.add_sum_removeNth i (fun j => y j)
      simpa [hi, Fin.removeNth] using hsum.trans_le hy.2
    · ext j
      induction j using i.succAboveCases <;> simp [facetEmbedding, hi]

theorem simplexFacet_coordinate_area (n : ℕ) (i : Fin (n + 1)) :
    Measure.euclideanHausdorffMeasure n (simplexFacet (n + 1) (some i)) =
      ENNReal.ofReal (1 / (Nat.factorial n : ℝ)) := by
  rw [← facetEmbedding_zero_image n i]
  have h := (facetEmbedding n i 0).euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (standardSimplex n)
  simpa only [finrank_euclideanSpace_fin, facetEmbedding_normDet_zero, ENNReal.ofReal_one,
    one_mul, standardSimplex_volume] using h

def diagonalFacetChart (n : ℕ) (i : Fin (n + 1)) (x : Euclidean n) : Euclidean (n + 1) :=
  WithLp.toLp 2 (i.insertNth (1 - ∑ j, x j) x)

theorem diagonalFacetChart_eq (n : ℕ) (i : Fin (n + 1)) (x : Euclidean n) :
    diagonalFacetChart n i x = facetEmbedding n i (-1) x + EuclideanSpace.single i 1 := by
  ext j
  induction j using i.succAboveCases <;>
    simp [diagonalFacetChart, facetEmbedding, sub_eq_add_neg, add_comm]

theorem diagonalFacetChart_image (n : ℕ) (i : Fin (n + 1)) :
    diagonalFacetChart n i '' standardSimplex n = simplexFacet (n + 1) none := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_standardSimplex_iff] at hx
    change diagonalFacetChart n i x ∈ standardSimplex (n + 1) ∧
      1 - ∑ j, diagonalFacetChart n i x j = 0
    rw [mem_standardSimplex_iff]
    simp [diagonalFacetChart, Fin.forall_iff_succAbove i]
    exact ⟨hx.2, hx.1⟩
  · rintro ⟨hy, hi⟩
    change 1 - ∑ j, y j = 0 at hi
    have htotal : ∑ j, y j = 1 := by linarith
    rw [mem_standardSimplex_iff] at hy
    have hsum := Fin.add_sum_removeNth i (fun j => y j)
    refine ⟨WithLp.toLp 2 (i.removeNth y), ?_, ?_⟩
    · rw [mem_standardSimplex_iff]
      refine ⟨fun j => hy.1 (i.succAbove j), ?_⟩
      change ∑ j, i.removeNth (fun k => y k) j ≤ 1
      linarith [hy.1 i]
    · ext j
      induction j using i.succAboveCases
      · simp only [diagonalFacetChart, PiLp.toLp_apply, Fin.insertNth_apply_same]
        change 1 - ∑ j, i.removeNth (fun k => y k) j = y i
        linarith
      · simp [diagonalFacetChart]

theorem simplexFacet_diagonal_area (n : ℕ) :
    Measure.euclideanHausdorffMeasure n (simplexFacet (n + 1) none) =
      ENNReal.ofReal (Real.sqrt (n + 1) / (Nat.factorial n : ℝ)) := by
  let i : Fin (n + 1) := Fin.last n
  rw [← diagonalFacetChart_image n i]
  have hset : diagonalFacetChart n i '' standardSimplex n =
      (IsometryEquiv.vaddConst (EuclideanSpace.single i (1 : ℝ))) ''
        (facetEmbedding n i (-1) '' standardSimplex n) := by
    rw [image_image]
    congr 1
    funext x
    exact diagonalFacetChart_eq n i x
  rw [hset, (IsometryEquiv.vaddConst (EuclideanSpace.single i (1 : ℝ))).isometry.euclideanHausdorffMeasure_image]
  have h := (facetEmbedding n i (-1)).euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (standardSimplex n)
  simp only [finrank_euclideanSpace_fin, facetEmbedding_normDet_neg_one,
    standardSimplex_volume] at h
  rw [h, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  ring

end Paper092

end

end OAI
