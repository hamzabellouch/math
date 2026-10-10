import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.LinkStarMatrix
import OAI.Combinatorics.TriangleRemoval.Spectral.MatrixRowAbsSum

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

theorem averagingProjector_infty_le_one {I : Type*} [Fintype I] :
    ‖(averagingProjector : Matrix I I ℝ)‖ ≤ 1 := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ zero_le_one
  intro i
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  simp [averagingProjector,abs_of_pos (inv_pos.mpr hcard),ne_of_gt hcard]

theorem globalStarAverage_infty_le_two {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) :
    ‖globalStarAverage G‖ ≤ 2 := by
  have h := sum_star_infty_norm_bound (edgeStar G) (fun _ => averagingProjector)
    1 2 (by norm_num) (by norm_num) (fun _ => averagingProjector_infty_le_one)
    (fun e => by rw [edgeStar_exact_overlap G hG e]; norm_num)
  simpa only [globalStarAverage,mul_one] using h

theorem goodPrefix_global_infty {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • globalLinkAdjacency G h.1‖ ≤ 4 := by
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hD
  have hlocal : ∀ u, ‖(prefixD n)⁻¹ • linkStarMatrix G h.1 u‖ ≤ 2 := by
    intro u
    change ‖Matrix.reindex (neighborEdgeEquiv G h.1 u) (neighborEdgeEquiv G h.1 u)
      ((prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ)‖ ≤ 2
    apply (infty_reindex_norm_le _ _).trans
    apply matrix_norm_le_of_row_abs_sum_le _ _ (by norm_num)
    intro v
    have hr := (abs_le.mp (goodPrefix_link_rows h u v)).2
    have hdeg : ((Finset.univ.filter ((linkSimpleGraph G h.1 u).Adj v)).card : ℝ) ≤
        2 * prefixD n := by
      nlinarith [mul_le_mul_of_nonneg_right hδ hD0.le]
    have heq : ∑ j : neighbors G u,
        |((prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ) v j| =
        (prefixD n)⁻¹ * ((Finset.univ.filter ((linkSimpleGraph G h.1 u).Adj v)).card : ℝ) := by
      simp only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hD0)]
      rw [← Finset.mul_sum]
      congr 1
      simp only [SimpleGraph.adjMatrix_apply]
      simp only [apply_ite abs,abs_one,abs_zero,Finset.sum_boole]
    rw [heq]
    calc
      _ ≤ (prefixD n)⁻¹ * (2 * prefixD n) :=
        mul_le_mul_of_nonneg_left hdeg (inv_nonneg.mpr hD0.le)
      _ = 2 := by field_simp
  have hsplit : (prefixD n)⁻¹ • globalLinkAdjacency G h.1 =
      ∑ u, extendStar (edgeStar G u) ((prefixD n)⁻¹ • linkStarMatrix G h.1 u) := by
    simp [globalLinkAdjacency,Finset.smul_sum,extendStar,Matrix.smul_mul,Matrix.mul_smul]
  rw [hsplit]
  simpa only [show (2 : ℝ)*2 = 4 by norm_num] using
    sum_star_infty_norm_bound (edgeStar G) _ 2 2 (by norm_num) (by norm_num) hlocal
    (fun e => by rw [edgeStar_exact_overlap G h.1 e]; norm_num)

theorem goodPrefix_residual_infty {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • globalLinkAdjacency G h.1 - globalStarAverage G‖ ≤ 6 := by
  have ha := goodPrefix_global_infty h hD hδ
  have hp := globalStarAverage_infty_le_two G h.1
  exact (norm_sub_le _ _).trans (by linarith)

end SharpTerminalLeave

end

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

end

end OAI
