import OAI.MeasureTheory.Falconer.Angular.GnomonicPairGram
import Mathlib.LinearAlgebra.CrossProduct

namespace OAI

/-! # Three-dimensional dual directions and the Gram determinant -/

namespace Falconer
open scoped Matrix

noncomputable def euclideanCross (u v : Space 3) : Space 3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

theorem euclidean_inner_dot (u v : Space 3) :
    inner ℝ u v = (WithLp.ofLp u) ⬝ᵥ (WithLp.ofLp v) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem inner_self_euclideanCross (u v : Space 3) : inner ℝ u (euclideanCross u v) = 0 := by
  rw [euclidean_inner_dot]
  exact dot_self_cross _ _

theorem inner_euclideanCross_self (u v : Space 3) : inner ℝ v (euclideanCross u v) = 0 := by
  rw [euclidean_inner_dot]
  exact dot_cross_self _ _

theorem euclideanCross_cyclic (u v w : Space 3) :
    inner ℝ u (euclideanCross v w) = inner ℝ v (euclideanCross w u) := by
  rw [euclidean_inner_dot,euclidean_inner_dot]
  exact triple_product_permutation _ _ _

theorem euclideanCross_norm_sq (u v : Space 3) :
    ‖euclideanCross u v‖^2 = pairGram u v := by
  rw [← real_inner_self_eq_norm_sq,euclidean_inner_dot]
  change (WithLp.ofLp u ⨯₃ WithLp.ofLp v) ⬝ᵥ
    (WithLp.ofLp u ⨯₃ WithLp.ofLp v) = _
  rw [cross_dot_cross,← euclidean_inner_dot,← euclidean_inner_dot,
    ← euclidean_inner_dot,← euclidean_inner_dot,real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  unfold pairGram
  simp only [real_inner_comm]
  ring

theorem euclideanCross_norm_le_one {u v : Space 3} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖euclideanCross u v‖ ≤ 1 := by
  have hh := euclideanCross_norm_sq u v
  have hp : ‖u‖^2*‖v‖^2 ≤ 1 := by
    calc
      _ ≤ (1:ℝ)^2*1^2 := by gcongr
      _ = _ := by norm_num
  unfold pairGram at hh
  nlinarith [sq_nonneg (inner ℝ u v),norm_nonneg (euclideanCross u v)]

theorem gram_eq_rowMatrix_mul_transpose (v : Fin 3 → Space 3) :
    Matrix.gram ℝ v = Matrix.of (fun i j => (v i j : ℝ)) *
      (Matrix.of (fun i j => (v i j : ℝ)))ᵀ := by
  ext i j
  simp only [Matrix.gram_apply,euclidean_inner_dot,Matrix.mul_apply,Matrix.transpose_apply,
    dotProduct,Matrix.of_apply]

theorem euclideanCross_triple_sq (u v w : Space 3) :
    (inner ℝ u (euclideanCross v w))^2 = tripleGram u v w := by
  have hs : inner ℝ u (euclideanCross v w) =
      Matrix.det (Matrix.of (fun i j => ((![u,v,w] i) j : ℝ))) := by
    rw [euclidean_inner_dot]
    change (WithLp.ofLp u) ⬝ᵥ ((WithLp.ofLp v) ⨯₃ (WithLp.ofLp w)) = _
    rw [triple_product_eq_det]
    rfl
  rw [hs,tripleGram,gram_eq_rowMatrix_mul_transpose,Matrix.det_mul,Matrix.det_transpose,pow_two]

end Falconer

end OAI
