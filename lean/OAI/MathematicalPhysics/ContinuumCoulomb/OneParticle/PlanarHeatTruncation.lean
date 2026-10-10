import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarResolvent

namespace OAI

/-! Explicit time truncation for the actual resolvent representation.
The omitted short-time interval costs at most its length; the long-time
tail is at most the elementary exponential tail. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarTruncatedHeat (r : PlanarPosition) (η T : ℝ) : ℝ :=
  ∫ t in η..T, Real.exp (-t) * planarHeatAverage t r

theorem planarHeatTime_nonnegative (r : PlanarPosition) {t : ℝ} (ht : 0 < t) :
    0 ≤ Real.exp (-t) * planarHeatAverage t r :=
  mul_nonneg (Real.exp_pos _).le (planarHeatAverage_positive ht r).le

theorem planarHeatTime_le_exp (r : PlanarPosition) {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) * planarHeatAverage t r ≤ Real.exp (-t) :=
  mul_le_of_le_one_right (Real.exp_pos _).le (planarHeatAverage_le_one ht r)

theorem planarHeatTime_short (r : PlanarPosition) {η : ℝ} (hη : 0 ≤ η) :
    |∫ t in (0 : ℝ)..η, Real.exp (-t) * planarHeatAverage t r| ≤ η := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => Real.exp (-t) * planarHeatAverage t r) (a := 0) (b := η) (C := 1)
    (by
      intro t ht
      have ht' : t ∈ Set.Ioc (0 : ℝ) η := by simpa only [Set.uIoc_of_le hη] using ht
      rw [Real.norm_eq_abs, abs_of_nonneg (planarHeatTime_nonnegative r ht'.1)]
      exact (planarHeatTime_le_exp r ht'.1).trans
        (Real.exp_le_one_iff.mpr (by linarith [ht'.1])))
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hη, one_mul] using h

theorem planarHeatTime_tail (r : PlanarPosition) {T : ℝ} (hT : 0 ≤ T) :
    |∫ t in Set.Ioi T, Real.exp (-t) * planarHeatAverage t r| ≤ Real.exp (-T) := by
  have hn : 0 ≤ ∫ t in Set.Ioi T, Real.exp (-t) * planarHeatAverage t r :=
    integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact planarHeatTime_nonnegative r (lt_of_le_of_lt hT ht))
  rw [abs_of_nonneg hn]
  have hi := (planarResolventMode_heat_integrable r).mono_set (Set.Ioi_subset_Ioi hT)
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi T) := by
    simpa only [neg_mul, one_mul] using exp_neg_integrableOn_Ioi T (by norm_num : (0 : ℝ) < 1)
  have hb := integral_mono_ae hi he (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact planarHeatTime_le_exp r (lt_of_le_of_lt hT ht))
  have ht : (∫ t in Set.Ioi T, Real.exp (-t)) = Real.exp (-T) := by
    simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T
  exact hb.trans_eq ht

theorem planarTruncatedHeat_error (r : PlanarPosition) {η T : ℝ}
    (hη : 0 ≤ η) (hηT : η ≤ T) :
    |planarResolventMode r - planarTruncatedHeat r η T| ≤ η + Real.exp (-T) := by
  let f := fun t => Real.exp (-t) * planarHeatAverage t r
  have hi : IntegrableOn f (Set.Ioi 0) := planarResolventMode_heat_integrable r
  have hηi : IntegrableOn f (Set.Ioi η) := hi.mono_set (Set.Ioi_subset_Ioi hη)
  have hT : 0 ≤ T := hη.trans hηT
  have hfirst := intervalIntegral.integral_Ioi_sub_Ioi hi hη
  have hsecond := intervalIntegral.integral_Ioi_sub_Ioi hηi hηT
  have heq : planarResolventMode r - planarTruncatedHeat r η T =
      (∫ t in (0 : ℝ)..η, f t) + ∫ t in Set.Ioi T, f t := by
    rw [planarResolventMode_heat_representation]
    unfold planarTruncatedHeat
    change (∫ t in Set.Ioi 0, f t) - (∫ t in η..T, f t) = _
    linarith
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (planarHeatTime_short r hη) (planarHeatTime_tail r hT))

end ContinuumCoulomb

end

end OAI
