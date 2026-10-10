import Mathlib
import OAI.NumberTheory.Ostmann.Construction.LogCellDefs
import OAI.NumberTheory.Ostmann.Section07SmoothPartition

namespace OAI

open MeasureTheory
namespace Ostmann.Construction

noncomputable def realLogCellWeight (c t : ℝ) : ℝ :=
  Ostmann.smoothPartition (Real.log t-c)/t

noncomputable def realLogCellDerivative (c t : ℝ) : ℝ :=
  (deriv Ostmann.smoothPartition (Real.log t-c)-Ostmann.smoothPartition (Real.log t-c))/t^2

lemma realLogCellWeight_hasDerivAt (c t : ℝ) (ht : 0 < t) :
    HasDerivAt (realLogCellWeight c) (realLogCellDerivative c t) t := by
  have hφ := (Ostmann.smoothPartition_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
    (x := Real.log t-c)
  have h := (hφ.comp t ((Real.hasDerivAt_log ht.ne').sub_const c)).div
    (hasDerivAt_id t) ht.ne'
  convert h using 1
  · funext x
    rfl
  · simp only [realLogCellDerivative, Function.comp_apply, id_eq, mul_one,
      mul_assoc, inv_mul_cancel₀ ht.ne']

lemma realLogCellWeight_continuousOn (c a b : ℝ) (ha : 0 < a) :
    ContinuousOn (realLogCellWeight c) (Set.Icc a b) := by
  intro t ht
  exact (realLogCellWeight_hasDerivAt c t (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt

lemma realLogCellDerivative_continuousOn (c a b : ℝ) (ha : 0 < a) :
    ContinuousOn (realLogCellDerivative c) (Set.Icc a b) := by
  have hd : Continuous (deriv Ostmann.smoothPartition) :=
    Ostmann.smoothPartition_contDiff.continuous_deriv (by simp)
  have hl0 : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun t ht =>
      show t ≠ 0 from ne_of_gt (lt_of_lt_of_le ha ht.1))
  have hl : ContinuousOn (fun t : ℝ => Real.log t-c) (Set.Icc a b) :=
    hl0.sub continuousOn_const
  exact ((hd.comp_continuousOn hl).sub
    (Ostmann.smoothPartition_continuous.comp_continuousOn hl)).div
      (continuousOn_id.pow 2) (fun t ht => pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le ha ht.1)))

lemma realLogCellWeight_endpoints (c : ℝ) :
    realLogCellWeight c (Real.exp (c-1)) = 0 ∧
      realLogCellWeight c (Real.exp (c+1)) = 0 := by
  constructor <;> simp only [realLogCellWeight, Real.log_exp]
  · rw [show c-1-c=(-1:ℝ) by ring,
      Ostmann.smoothPartition_zero_of_one_le_abs (by norm_num), zero_div]
  · rw [show c+1-c=(1:ℝ) by ring,
      Ostmann.smoothPartition_zero_of_one_le_abs (by norm_num), zero_div]

lemma realLogCellWeight_integral (c : ℝ) :
    (∫ t in Real.exp (c-1)..Real.exp (c+1), realLogCellWeight c t) = 1 := by
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := c-1) (b := c+1) (f := Real.exp) (f' := Real.exp)
    (g := realLogCellWeight c) (fun t _ => Real.hasDerivAt_exp t)
    Real.continuous_exp.continuousOn (by
      intro x hx
      obtain ⟨u,hu,rfl⟩ := hx
      exact (realLogCellWeight_hasDerivAt c (Real.exp u) (Real.exp_pos u)).continuousAt.continuousWithinAt)
  have hleft : (∫ t in c-1..c+1, realLogCellWeight c (Real.exp t)*Real.exp t) = 1 := by
    simp only [realLogCellWeight, Real.log_exp, div_mul_cancel₀ _ (Real.exp_ne_zero _)]
    rw [intervalIntegral.integral_comp_sub_right]
    rw [show c-1-c=(-1:ℝ) by ring, show c+1-c=(1:ℝ) by ring]
    exact (intervalIntegral.integral_eq_integral_of_support_subset
      (Ostmann.smoothPartition_support_subset.trans Set.Ioo_subset_Ioc_self)).trans
        Ostmann.smoothPartition_integral
  exact hsub.symm.trans hleft

end Ostmann.Construction

end OAI
