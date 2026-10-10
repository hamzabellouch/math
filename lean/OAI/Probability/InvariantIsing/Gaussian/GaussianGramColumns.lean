import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResolvent

namespace OAI

/-! Exact column decomposition and the positive leave-one-column Gram matrix. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

def gaussianGramRawColumn {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) : Fin N → ℝ :=
  fun i => z (i,j)

def gaussianGramLeaveOneOut {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : Matrix (Fin N) (Fin N) ℝ :=
  (1/(N : ℝ)) • ∑ l ∈ Finset.univ.erase j, vecMulVec (gaussianGramRawColumn z l) (gaussianGramRawColumn z l)

lemma gaussianPatternCoupling_column_sum {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternCoupling 1 z = (1/(N : ℝ)) •
      ∑ j : Fin m, vecMulVec (gaussianGramRawColumn z j) (gaussianGramRawColumn z j) := by
  ext i k
  simp only [gaussianPatternCoupling,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,
    Matrix.transpose_apply,gaussianPatternArray,Matrix.sum_apply,Matrix.vecMulVec_apply,
    gaussianGramRawColumn]

lemma gaussianGramLeaveOneOut_posSemidef {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : (gaussianGramLeaveOneOut z j).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (by positivity : (0 : ℝ) ≤ 1/N)
  apply Matrix.posSemidef_sum
  intro l _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (gaussianGramRawColumn z l)

lemma gaussianGramLeaveOneOut_decomposition {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : gaussianPatternCoupling 1 z = gaussianGramLeaveOneOut z j+
      (1/(N : ℝ)) • vecMulVec (gaussianGramRawColumn z j) (gaussianGramRawColumn z j) := by
  rw [gaussianPatternCoupling_column_sum,gaussianGramLeaveOneOut,← smul_add]
  congr 1
  exact (Finset.sum_erase_add Finset.univ
    (fun l => vecMulVec (gaussianGramRawColumn z l) (gaussianGramRawColumn z l))
    (Finset.mem_univ j)).symm

end InvariantIsing

end

end OAI
