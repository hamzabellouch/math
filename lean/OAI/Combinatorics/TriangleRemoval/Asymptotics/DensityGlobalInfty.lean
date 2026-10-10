import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.AveragingProjectorInftyOne

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix.Norms.Operator
open Classical Matrix

namespace SharpTerminalLeave

theorem density_global_infty {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (D : ℝ) (hD0 : 0 < D)
    (hrow : ∀ u v : Fin n, {u,v} ∈ G → (currentCodegree G u v : ℝ) ≤ 2*D) :
    ‖D⁻¹ • globalLinkAdjacency G hG‖ ≤ 4 := by
  have hlocal : ∀ u, ‖(D)⁻¹ • linkStarMatrix G hG u‖ ≤ 2 := by
    intro u
    change ‖Matrix.reindex (neighborEdgeEquiv G hG u) (neighborEdgeEquiv G hG u)
      ((D)⁻¹ • (linkSimpleGraph G hG u).adjMatrix ℝ)‖ ≤ 2
    apply (infty_reindex_norm_le _ _).trans
    apply matrix_norm_le_of_row_abs_sum_le _ _ (by norm_num)
    intro v
    have hdeg : ((Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).card : ℝ) ≤ 2*D := by
      rw [link_degree_eq G hG u v]
      exact hrow u v.val (Finset.mem_filter.mp v.property).2
    have heq : ∑ j : neighbors G u,
        |((D)⁻¹ • (linkSimpleGraph G hG u).adjMatrix ℝ) v j| =
        (D)⁻¹ * ((Finset.univ.filter ((linkSimpleGraph G hG u).Adj v)).card : ℝ) := by
      simp only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hD0)]
      rw [← Finset.mul_sum]
      congr 1
      simp only [SimpleGraph.adjMatrix_apply]
      simp only [apply_ite abs,abs_one,abs_zero,Finset.sum_boole]
    rw [heq]
    calc
      _ ≤ (D)⁻¹ * (2 * D) :=
        mul_le_mul_of_nonneg_left hdeg (inv_nonneg.mpr hD0.le)
      _ = 2 := by field_simp
  have hsplit : (D)⁻¹ • globalLinkAdjacency G hG =
      ∑ u, extendStar (edgeStar G u) ((D)⁻¹ • linkStarMatrix G hG u) := by
    simp [globalLinkAdjacency,Finset.smul_sum,extendStar,Matrix.smul_mul,Matrix.mul_smul]
  rw [hsplit]
  simpa only [show (2 : ℝ)*2 = 4 by norm_num] using
    sum_star_infty_norm_bound (edgeStar G) _ 2 2 (by norm_num) (by norm_num) hlocal
    (fun e => by rw [edgeStar_exact_overlap G hG e]; norm_num)

lemma density_residual_infty {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (D : ℝ) (hD0 : 0 < D)
    (hrow : ∀ u v : Fin n, {u,v} ∈ G → (currentCodegree G u v : ℝ) ≤ 2*D) :
    ‖D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G‖ ≤ 6 := by
  have ha := density_global_infty G hG D hD0 hrow
  have hp := globalStarAverage_infty_le_two G hG
  exact (norm_sub_le _ _).trans (by linarith only [ha,hp])

end SharpTerminalLeave
end
end

end OAI
