import OAI.NumberTheory.Ostmann.Construction.LogCellCalculus
import OAI.NumberTheory.Ostmann.Section07SmoothPartitionDerivative

namespace OAI

open MeasureTheory
namespace Ostmann.Construction

lemma exists_logCell_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ,
      (∫ t in Real.exp (c-1)..Real.exp (c+1), t*|realLogCellDerivative c t|) ≤ C := by
  obtain ⟨M,hM,hbound⟩ := Ostmann.smoothPartition_deriv_sub_bound
  refine ⟨2*M, by positivity, ?_⟩
  intro c
  have ha : 0 < Real.exp (c-1) := Real.exp_pos _
  have hb : 0 < Real.exp (c+1) := Real.exp_pos _
  have hab : Real.exp (c-1) ≤ Real.exp (c+1) := Real.exp_le_exp.mpr (by linarith)
  have hgi : IntervalIntegrable (fun t => t*|realLogCellDerivative c t|)
      volume (Real.exp (c-1)) (Real.exp (c+1)) :=
    (continuous_id.continuousOn.mul
      (realLogCellDerivative_continuousOn c _ _ ha).abs).intervalIntegrable_of_Icc hab
  have hri : IntervalIntegrable (fun t : ℝ => M/t) volume (Real.exp (c-1)) (Real.exp (c+1)) :=
    (continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (lt_of_lt_of_le ha ht.1))).intervalIntegrable_of_Icc hab
  calc
    _ ≤ ∫ t in Real.exp (c-1)..Real.exp (c+1), M/t := by
      apply intervalIntegral.integral_mono_on hab hgi hri
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      rw [realLogCellDerivative, abs_div, abs_pow, abs_of_pos ht0]
      have heq : t*(|deriv Ostmann.smoothPartition (Real.log t-c)-
          Ostmann.smoothPartition (Real.log t-c)|/t^2) =
          |deriv Ostmann.smoothPartition (Real.log t-c)-
            Ostmann.smoothPartition (Real.log t-c)|/t := by field_simp
      rw [heq]
      exact div_le_div_of_nonneg_right (hbound _) ht0.le
    _ = M*Real.log (Real.exp (c+1)/Real.exp (c-1)) := by
      simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul,
        integral_inv_of_pos ha hb]
    _ = 2*M := by
      rw [Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
      ring

end Ostmann.Construction

end OAI
