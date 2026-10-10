import OAI.Geometry.ProjectionBody.GraphChart
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- The Jacobian of a graph chart is the length of its unnormalized normal. -/
theorem graphLinear_normDet {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    (graphLinear i a).normDet = ‖graphNormal i a‖ := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hGram : Matrix.gram ℝ (fun j => graphLinear i a (b j)) =
      1 + Matrix.replicateCol Unit (fun j => a j) *
        Matrix.replicateRow Unit (fun j => a j) := by
    ext j k
    rw [Matrix.gram_apply, graphLinear_inner]
    simp [b, EuclideanSpace.basisFun_apply, eq_comm,
      EuclideanSpace.inner_single_right, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
  have hsquare : (graphLinear i a).normDet ^ 2 = ‖graphNormal i a‖ ^ 2 := by
    calc
      (graphLinear i a).normDet ^ 2 =
          (Matrix.gram ℝ (fun j => graphLinear i a (b j))).det :=
        (graphLinear i a).normDet_sq_eq_det_gram b
      _ = ‖graphNormal i a‖ ^ 2 := by
        rw [hGram, Matrix.det_one_add_replicateCol_mul_replicateRow,
          graphNormal_norm_sq, EuclideanSpace.real_norm_sq_eq]
        simp [dotProduct, pow_two]
  exact (sq_eq_sq₀ (graphLinear i a).normDet_nonneg (norm_nonneg _)).mp hsquare

end ProjectionCounterexample

end

end OAI
