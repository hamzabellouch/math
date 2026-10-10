import OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand
import OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent.LiteralAnalytic
open DeterminantContradiction

theorem actual_minor_expansion {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det =
      ∑ f : ChoiceFamily d H, (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det := by
  classical
  have hp : ∀ r c : Row d H,
      (MatrixTranslation.periodMonomial r.1.val logarithmicPeriod
        ((selection c).1 0) (fun i => (selection c).1 i.succ)).support ⊆
        MatrixTranslation.transverseIndices (fixedWeights d) H := by
    intro r c
    apply MatrixTranslation.periodMonomial_support_subset _ _ _ _ _ _ (fixedWeights_pos d)
    have hc := InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c)
    have hz : 0 ≤ (d.w0 : ℝ) * ((selection c).1 0 : ℝ) :=
      mul_nonneg d.w0_pos.le (Nat.cast_nonneg _)
    linarith
  have he := MatrixTranslation.det_matrix_translation
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (fun r : Row d H => r.1.val) (fun r => r.2.1 0) logarithmicPeriod
    (fun r i => r.2.1 i.succ) (fun c => (selection c).1 0)
    (fun c i => (selection c).1 i.succ) (MatrixTranslation.transverseIndices (fixedWeights d) H) hp
  convert! he using 1

theorem card_choiceFamily_le {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Fintype.card (ChoiceFamily d H) ≤ translationTermCount d.m d.v0 H ^ actualRowCount d H := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _r : Row d H, translationTermCount d.m d.v0 H := by
      apply Finset.prod_le_prod
      intro r _
      exact MatrixTranslation.row_term_count (fixedWeights d) H d.v0
        (fun i => by change 1 ≤ MatrixArithmetic.logWeights (finiteDenominators d) i
                     rw [logWeights_eq]; exact d.x_one_le _)
        (beta d r) (r.2.1 0) (rowOrder_le d r)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, actualRowCount]

noncomputable def analyticRemainder {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  Collision.collisionRemainder (actualRowCount d H) H +
    Real.log (translationTermCount d.m d.v0 H : ℝ) / H

theorem actual_minor_analytic_bound {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      d.analyticError + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) := by
  have hQ : (0 : ℝ) < translationTermCount d.m d.v0 H := by
    unfold translationTermCount
    positivity
  have hc : (Fintype.card (ChoiceFamily d H) : ℝ) ≤
      (translationTermCount d.m d.v0 H : ℝ) ^ actualRowCount d H := by
    exact_mod_cast card_choiceFamily_le d H
  have hb := DeterminantAnalyticBound.log_norm_sum_le
    (fun f : ChoiceFamily d H => (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det)
    (actualMinor d H selection).det (actualRowCount_pos d hH) hH hQ hc
    (actual_minor_expansion d selection) hne (norm_actual_summand_le d hnu hH selection)
  convert! hb using 1
  unfold analyticRemainder
  ring

theorem tendsto_analyticRemainder {nu : ℝ} (d : FixedData nu) :
    Tendsto (analyticRemainder d) atTop (𝓝 0) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.base.theta := by exact_mod_cast d.base.theta_pos
  have hcount := MatrixCounting.tendsto_rowCount_normalized d.K d.v0 d.base.theta
    (finiteDenominators d) hv ht (finiteDenominators_two_le d)
  have hlead : 0 < (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
        ∏ i, MatrixArithmetic.logWeights (finiteDenominators d) i) := by
    apply div_pos
    · apply mul_pos
      · exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one d.K_pos
      · exact pow_pos d.base.theta_pos _
    · apply mul_pos
      · exact mul_pos (by positivity) d.v0_pos
      · exact Finset.prod_pos (fun i _ => fixedWeights_pos d i)
  have hr := tendsto_collisionRemainder_of_normalized_pow
    (M := actualRowCount d) hcount hlead
  have hq := tendsto_log_translationTermCount_div d.m d.v0_pos
  convert! hr.add hq using 1
  norm_num

theorem analyticAggregate : AnalyticAggregateStatement := by
  intro nu hnu d
  refine ⟨analyticRemainder d, tendsto_analyticRemainder d, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  intro selection hne
  exact actual_minor_analytic_bound d (by linarith) hH selection hne

end PiExponent.LiteralAnalytic

end OAI
