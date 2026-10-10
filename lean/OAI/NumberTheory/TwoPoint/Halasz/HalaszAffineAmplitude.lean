import OAI.NumberTheory.TwoPoint.Halasz.HalaszStationaryPhase
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace OAI

/-! Affine amplitudes for the two pieces of a compact triangular weight. -/
namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_affine_amplitude_bound (f : ℝ → ℂ) (a b m c B : ℝ)
    (hab : a ≤ b) (hi : IntervalIntegrable f volume a b)
    (hc : ∀ x ∈ Set.Icc a b, ContinuousAt f x) (hm : StronglyMeasurable f)
    (hB : ∀ x ∈ Set.Icc a b, ‖∫ y in a..x, f y‖ ≤ B) :
    ‖∫ x in a..b, (m*x+c : ℝ)*f x‖ ≤ (|m*b+c|+|m| *(b-a))*B := by
  let F : ℝ → ℂ := fun x => ∫ y in a..x, f y
  have hF : ContinuousOn F (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hi (Set.left_mem_uIcc)
  have hdF (x : ℝ) (hx : x ∈ Set.Icc a b) : HasDerivAt F (f x) x := by
    apply intervalIntegral.integral_hasDerivAt_right
      (hi.mono_set (by simpa only [Set.uIcc_of_le hab, Set.uIcc_of_le hx.1] using
        Set.Icc_subset_Icc le_rfl hx.2))
      hm.stronglyMeasurableAtFilter (hc x hx)
  have hdm (x : ℝ) : HasDerivAt (fun y : ℝ => (m*y+c : ℂ)) (m:ℂ) x := by
    convert (((hasDerivAt_id x).const_mul m).add_const c).ofReal_comp using 1 <;> simp
  have hmc : ContinuousOn (fun x : ℝ => (m*x+c : ℂ)) (Set.uIcc a b) :=
    (continuous_const.mul Complex.continuous_ofReal |>.add continuous_const).continuousOn
  have hmi : IntervalIntegrable (fun _ : ℝ => (m:ℂ)) volume a b := intervalIntegrable_const
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hmc hF
    (fun x _ => hdm x)
    (fun x hx => hdF x (by
      rw [min_eq_left hab, max_eq_right hab] at hx
      exact ⟨hx.1.le, hx.2.le⟩)) hmi hi
  change (∫ x in a..b, (m*x+c : ℂ)*f x) = _ at he
  have hzero : F a = 0 := intervalIntegral.integral_same
  rw [hzero, mul_zero, sub_zero] at he
  have hnorm : ‖∫ x in a..b, (m:ℂ)*F x‖ ≤ |m| *B*(b-a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := |m| *B) (f := fun x => (m:ℂ)*F x) (by
        intro x hx
        have hx' : x ∈ Set.Icc a b := by
          rw [Set.uIoc_of_le hab] at hx
          exact ⟨hx.1.le, hx.2⟩
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB x hx') (abs_nonneg m))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  have hb := hB b ⟨hab, le_rfl⟩
  have hprod : ‖(m*b+c : ℂ)*F b‖ ≤ |m*b+c| *B := by
    rw [norm_mul]
    norm_cast
    simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hb (abs_nonneg (m*b+c))
  push_cast
  rw [he]
  exact (norm_sub_le _ _).trans (by nlinarith)

lemma halasz_log_stationary_affine (u v a b m c : ℝ) (hu : 0 < u)
    (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, (m*x+c : ℝ)*halaszLogPhase u v x‖ ≤
      (|m*b+c|+|m| *(b-a))*(10*b/Real.sqrt u) := by
  apply halasz_affine_amplitude_bound _ _ _ _ _ _ hab
    ((halasz_log_phase_continuousOn u v a b ha).intervalIntegrable_of_Icc hab)
    (fun x hx => (halasz_log_phase_deriv u v x (ha.trans_le hx.1).ne').continuousAt)
    (by
      have hm : Measurable (halaszLogPhase u v) := by unfold halaszLogPhase; fun_prop
      exact hm.stronglyMeasurable)
  intro x hx
  exact (halasz_log_stationary_integral u v a x hu ha hx.1).trans
    (div_le_div_of_nonneg_right (by linarith [hx.2]) (Real.sqrt_nonneg u))

end TwoPointCorrelations

end OAI
