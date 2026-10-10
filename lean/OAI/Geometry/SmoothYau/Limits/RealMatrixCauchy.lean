import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma real_matrix_cauchy {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (v w : ι → ℝ) :
    (v ⬝ᵥ (A *ᵥ w)) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (w ⬝ᵥ (A *ᵥ w)) := by
  have hs : Aᵀ = A := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have he : w ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ w) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs]
  have hp (t : ℝ) : 0 ≤ (v ⬝ᵥ (A *ᵥ v)) * (t * t) +
      (2 * (v ⬝ᵥ (A *ᵥ w))) * t + (w ⬝ᵥ (A *ᵥ w)) := by
    have h := hA.dotProduct_mulVec_nonneg (t • v + w)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h
    rw [he] at h
    nlinarith [h]
  have h := discrim_le_zero hp
  dsimp [discrim] at h
  nlinarith

lemma real_dual_matrix_cauchy {A : Matrix ι ι ℝ} (hA : A.PosDef) (p z : ι → ℝ) :
    (p ⬝ᵥ z) ^ 2 ≤ (p ⬝ᵥ (A⁻¹ *ᵥ p)) * (z ⬝ᵥ (A *ᵥ z)) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hc : A *ᵥ (A⁻¹ *ᵥ p) = p := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hs : Aᵀ = A := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have he : (A⁻¹ *ᵥ p) ⬝ᵥ (A *ᵥ z) = p ⬝ᵥ z := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, hc]
  have h := real_matrix_cauchy hA.posSemidef (A⁻¹ *ᵥ p) z
  rw [hc, he, dotProduct_comm (A⁻¹ *ᵥ p) p] at h
  exact h

lemma rank_one_mulVec_inverse_direction {A : Matrix ι ι ℝ} (hA : IsUnit A.det)
    (p : ι → ℝ) (a b : ℝ) :
    (a • A + b • Matrix.vecMulVec p p) *ᵥ (A⁻¹ *ᵥ p) =
      (a + b * (p ⬝ᵥ (A⁻¹ *ᵥ p))) • p := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  ring

lemma det_add_vecMulVec {A : Matrix ι ι ℝ} (hA : IsUnit A.det) (u v : ι → ℝ) :
    (A + Matrix.vecMulVec u v).det = A.det * (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have he : Matrix.vecMulVec u v = Matrix.replicateCol Unit u * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec]
  rw [he, Matrix.det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma det_rank_one_three {A : Matrix ι ι ℝ} (hA : IsUnit A.det)
    (hn : Fintype.card ι = 3) (p : ι → ℝ) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    (a • A + b • Matrix.vecMulVec p p).det =
      a ^ 2 * (a + b * (p ⬝ᵥ (A⁻¹ *ᵥ p))) * A.det := by
  have he : a • A + b • Matrix.vecMulVec p p =
      a • (A + Matrix.vecMulVec ((b / a) • p) p) := by
    rw [smul_add, Matrix.smul_vecMulVec, smul_smul]
    congr 1
    congr 1
    field_simp
  rw [he, Matrix.det_smul, hn, det_add_vecMulVec hA,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  field_simp

lemma rank_one_inverse_direction {A : Matrix ι ι ℝ} (hA : IsUnit A.det)
    (p : ι → ℝ) (a b : ℝ)
    (hB : IsUnit (a • A + b • Matrix.vecMulVec p p).det)
    (hc : a + b * (p ⬝ᵥ (A⁻¹ *ᵥ p)) ≠ 0) :
    (a • A + b • Matrix.vecMulVec p p)⁻¹ *ᵥ p =
      (a + b * (p ⬝ᵥ (A⁻¹ *ᵥ p)))⁻¹ • (A⁻¹ *ᵥ p) := by
  apply (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hB))
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec,
    Matrix.mulVec_smul, rank_one_mulVec_inverse_direction hA, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

end YauCounterexamples

end

end OAI
