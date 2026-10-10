import OAI.Probability.InvariantIsing.Cavity.CavityGramProbability
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

namespace OAI

/-! The finite Gaussian frame construction: normalize the column Gram
matrix by its positive square root. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityGaussianMatrix {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin q) ℝ :=
  fun k i => x k i / Real.sqrt n

lemma cavityGaussianMatrix_gram {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    (cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n =
      cavityEmpiricalGram x n := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cavityGaussianMatrix]
  simp_rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  rw [← Finset.sum_div]
  change (∑ k : Fin n, x k i * x k j) / (n : ℝ) =
    (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ)
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => x k i * x k j) n

lemma cavity_sqrt_det_isUnit {q : ℕ} (G : Matrix (Fin q) (Fin q) ℝ)
    (hG : G.PosDef) : IsUnit (CFC.sqrt G).det := by
  apply isUnit_iff_ne_zero.mpr
  have he : (CFC.sqrt G).det * (CFC.sqrt G).det = G.det := by
    rw [← Matrix.det_mul, CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
  intro hz
  rw [hz, zero_mul] at he
  exact hG.det_pos.ne' he.symm

def cavityNormalizeFrame {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ) :
    Matrix (Fin n) (Fin q) ℝ :=
  A * (CFC.sqrt (A.transpose * A))⁻¹

theorem cavityNormalizeFrame_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hG : (A.transpose * A).PosDef) :
    (cavityNormalizeFrame A).transpose * cavityNormalizeFrame A = 1 := by
  let G : Matrix (Fin q) (Fin q) ℝ := A.transpose * A
  let S : Matrix (Fin q) (Fin q) ℝ := CFC.sqrt G
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hs : S.transpose = S :=
    Matrix.isHermitian_iff_isSymm.mp hS.isHermitian
  have hss : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hu : IsUnit S.det := cavity_sqrt_det_isUnit G hG
  change (A * S⁻¹).transpose * (A * S⁻¹) = 1
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hs]
  calc
    S⁻¹ * A.transpose * (A * S⁻¹) = S⁻¹ * G * S⁻¹ := by
      simp only [G, Matrix.mul_assoc]
    _ = S⁻¹ * (S * S) * S⁻¹ := by rw [hss]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hu,
        Matrix.one_mul, Matrix.mul_nonsing_inv S hu]

theorem cavityNormalizeFrame_orthonormal {n q : ℕ}
    (A : Matrix (Fin n) (Fin q) ℝ) (hG : (A.transpose * A).PosDef) :
    Orthonormal ℝ (fun i : Fin q =>
      (WithLp.toLp 2 (fun k : Fin n => cavityNormalizeFrame A k i) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrArg (fun M : Matrix (Fin q) (Fin q) ℝ => M i j)
    (cavityNormalizeFrame_gram A hG)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

end InvariantIsing

end

end OAI
