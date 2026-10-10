import OAI.NumberTheory.JointDickman.Counting.ComplexFiniteShortAverages

namespace OAI

/-! # Local integrability of arbitrary arithmetic short averages -/
namespace JointDickman.PublishedInputs
open Finset Filter MeasureTheory Classical

theorem complexShortAverage_sq_integrable_any (f : ArithmeticFunction ℂ)
    {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖complexShortAverage f H z‖^2) volume a b := by
  let S := range (⌊max a b+H⌋₊+1)
  let K := (∑ n ∈ S, ‖f n‖)/H
  have hK : 0 ≤ K := div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)) hH.le
  refine (intervalIntegrable_const (c := K^2)).mono_fun'
    (((measurable_complexShortAverage f H).norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
  have hbnd : ‖complexShortAverage f H z‖ ≤ K := by
    rw [complexShortAverage,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
    apply div_le_div_of_nonneg_right _ hH.le
    refine (norm_sum_le _ _).trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _))
    intro n hn
    apply mem_range.mpr
    exact Nat.lt_succ_of_le ((mem_Ioc.mp hn).2.trans (Nat.floor_mono (by linarith [hz.2])))
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm,abs_of_nonneg hK] using
    pow_le_pow_left₀ (norm_nonneg _) hbnd 2

end JointDickman.PublishedInputs

end OAI
