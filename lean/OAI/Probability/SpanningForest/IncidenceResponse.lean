import OAI.Probability.SpanningForest.TransferCurrentLipschitz
import OAI.Probability.SpanningForest.ReducedLaplacian

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.TransferCurrent

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] in

lemma laplacian_reducedGradient (src dst : E → V) (root : V) (h : E → ℝ) :
    laplacian (ReducedLaplacian.reducedGradient src dst root) h =
      ReducedLaplacian.weightedLaplacian src dst root (fun e => Real.exp (h e)) := by
  ext i j
  simp [laplacian, ReducedLaplacian.weightedLaplacian, Matrix.mul_apply,
    Matrix.diagonal, Matrix.vecMulVec, Matrix.of_apply, Matrix.sum_apply, smul_eq_mul, mul_comm, mul_assoc]

lemma incidence_marginal_sub_le_half (src dst : E → V) (root : V)
    (hconn : ReducedLaplacian.Connected src dst) (h k : E → ℝ) (e : E)
    (D : ℝ) (hD : 0 ≤ D) (hdir : ∀ f, |k f - h f| ≤ D) :
    |marginal (ReducedLaplacian.reducedGradient src dst root) k e -
      marginal (ReducedLaplacian.reducedGradient src dst root) h e| ≤ (1 : ℝ) / 2 * D := by
  apply marginal_sub_le_half _ h k e D hD hdir
  intro t ht
  rw [laplacian_reducedGradient]
  exact ReducedLaplacian.weightedLaplacian_isUnit src dst root _ hconn
    (fun f => Real.exp_pos _)

end Problem336.TransferCurrent

end

end OAI
