import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.MatrixEntries
import OAI.Analysis.JiangSu.TraceCone.MatrixRestriction
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzCornerReflection

namespace OAI


noncomputable section
open scoped CStarAlgebra

namespace UnitalTomsWinter
open TraceCone

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixCornerProjection (n : ℕ) : MatrixLimit A := matrixLimitStage n 1

lemma matrixCornerProjection_isStarProjection (n : ℕ) :
    IsStarProjection (matrixCornerProjection (A := A) n) := by
  constructor
  · change matrixLimitStage n 1 * matrixLimitStage n 1 = matrixLimitStage n 1
    rw [← map_mul, one_mul]
  · change star (matrixLimitStage n 1) = matrixLimitStage n 1
    rw [← map_star, star_one]

lemma matrixInclusion_one_mul {n m : ℕ} (h : n ≤ m) (M : FinMatrix A m) :
    matrixInclusion h 1 * M * matrixInclusion h 1 = matrixMask n M := by
  apply CStarMatrix.ext; intro i j
  have hd : matrixInclusion h (1 : FinMatrix A n) =
      CStarMatrix.ofMatrix (Matrix.diagonal (fun i : Fin m => if i.val < n then (1 : A) else 0)) := by
    apply CStarMatrix.ext; intro i j
    simp only [matrixInclusion_entry, CStarMatrix.one_apply, Matrix.diagonal]
    split_ifs <;> simp_all [Fin.ext_iff]
    omega
  rw [hd]
  change (Matrix.diagonal (fun k : Fin m => if k.val < n then (1 : A) else 0) *
    CStarMatrix.ofMatrix.symm M *
    Matrix.diagonal (fun k : Fin m => if k.val < n then (1 : A) else 0)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [matrixMask_apply]
  split_ifs <;> simp_all

theorem matrixCompression_eq_corner (n : ℕ) (x : MatrixLimit A) :
    matrixCompression n x = matrixCornerProjection n * x * matrixCornerProjection n := by
  have hc : Continuous (matrixCompression (A := A) n) :=
    ((matrixCompression n).mkContinuous 1 (fun x => by simpa using matrixCompression_norm_le n x)).continuous
  have : ContinuousMul (MatrixLimit A) := NonUnitalSeminormedRing.toContinuousMul
  have hcorner : Continuous (fun value : MatrixLimit A =>
      matrixCornerProjection n * value * matrixCornerProjection n) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hclosed : IsClosed {value : MatrixLimit A |
      ‖matrixCompression n value - matrixCornerProjection n * value * matrixCornerProjection n‖ = 0} :=
    isClosed_eq (hc.sub hcorner).norm continuous_const
  refine finiteMatrixSubalgebra_dense.induction_on x
    (by simpa only [norm_eq_zero, sub_eq_zero] using hclosed) ?_
  intro y
  obtain ⟨m,M,rfl⟩ := finiteMatrixStage_surjective y
  change matrixCompression n (matrixLimitStage m M) =
    matrixLimitStage n 1 * matrixLimitStage m M * matrixLimitStage n 1
  let k := max n m
  have hn : n ≤ k := le_max_left _ _
  have hm : m ≤ k := le_max_right _ _
  rw [← matrixLimitStage_compatible hm M]
  change matrixCompression n (matrixLimitStage k (matrixInclusion hm M)) =
    matrixLimitStage n 1 * matrixLimitStage k (matrixInclusion hm M) * matrixLimitStage n 1
  rw [← matrixLimitStage_compatible hn 1, ← map_mul, ← map_mul,
    matrixInclusion_one_mul, matrixCompression_stage]

theorem matrixLimitStage_full_corner (n : ℕ) (x : MatrixLimit A)
    (hx : matrixLimitStage n 1 * x * matrixLimitStage n 1 = x) :
    ∃ M : FinMatrix A n, matrixLimitStage n M = x := by
  obtain ⟨M,hM⟩ := matrixCompression_range n x
  exact ⟨M,hM.trans ((matrixCompression_eq_corner n x).trans hx)⟩

theorem cuntzSubequiv_reflect_matrixLimit {n : ℕ} {a b : FinMatrix A n}
    (h : CuntzSubequiv (matrixLimitStage n a) (matrixLimitStage n b)) : CuntzSubequiv a b := by
  exact CuntzSubequiv.reflect_corner (matrixLimitStage (A := A) n)
    (matrixLimitStage_isometry (A := A) n).injective (matrixLimitStage_full_corner n) h
end UnitalTomsWinter
end

end OAI
