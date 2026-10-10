import Mathlib
import OAI.Probability.SKBarriers.Scalar.DyadicScalar
import OAI.Probability.SKBarriers.Hierarchy.TimeChainPressureAlgebra

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicIntervals_duration (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    chainDuration (dyadicIntervals α n s t)=t := by
  induction n generalizing s t with
  | zero => simp [dyadicIntervals,chainDuration]
  | succ n ih =>
    simp only [dyadicIntervals,chainDuration,List.map_append,List.sum_append] at *
    rw [ih,ih]
    exact add_halves t

theorem dyadicPenalty_error {α : ℝ → ℝ} (hα : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (hs : 0 ≤ s) (ht : s+t ≤ 1) :
    |chainQuadraticPenalty s (dyadicIntervals α n s t)-2*∫ u in s..s+t, u*α u| ≤
      2*(t:ℝ)/(2:ℝ)^n*(α (s+t)-α s) := by
  have hi (a b : ℝ) : IntervalIntegrable (fun u => u*α u) volume a b :=
    hα.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
  induction n generalizing s t with
  | zero =>
    have hst : s ≤ s+(t:ℝ) := by linarith [t.coe_nonneg]
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=s) (b:=s+t)
      (f:=fun u => 2*u*(α u-α s)) (C:=2*(α (s+t)-α s)) (by
        intro u hu
        rw [uIoc_of_le hst] at hu
        have ha := hα hu.1.le
        have hb := hα hu.2
        have hu0 : 0 ≤ u := hs.trans hu.1.le
        have hu1 : u ≤ 1 := hu.2.trans ht
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hb) hu0,
          mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hu1)])
    have he : (∫ u in s..s+t, 2*u*(α u-α s))=
        2*(∫ u in s..s+t, u*α u)-α s*((s+t)^2-s^2) := by
      simp_rw [show ∀ u : ℝ, 2*u*(α u-α s)=2*(u*α u)-2*(u*α s) by intro u; ring]
      have hic : IntervalIntegrable (fun u : ℝ => 2*(u*α s)) volume s (s+t) :=
        ((continuous_id.intervalIntegrable s (s+t)).mul_const (α s)).const_mul 2
      rw [intervalIntegral.integral_sub ((hi s (s+t)).const_mul 2) hic,
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_mul_const,integral_id]
      ring
    rw [he,Real.norm_eq_abs,abs_sub_comm,add_sub_cancel_left,abs_of_nonneg t.coe_nonneg] at H
    simpa only [dyadicIntervals,chainQuadraticPenalty_singleton,pow_zero,div_one,mul_comm (2*(α (s+t)-α s)) (t:ℝ),mul_assoc,mul_left_comm] using H
  | succ n ih =>
    have hc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have he : s+(t:ℝ)/2+(t:ℝ)/2=s+t := by ring
    have hmid : 0 ≤ s+(t:ℝ)/2 := by positivity
    have hmid1 : s+(t/2:ℝ≥0) ≤ 1 := by rw [hc]; linarith [t.coe_nonneg]
    have hend1 : s+(t:ℝ)/2+(t/2:ℝ≥0) ≤ 1 := by rw [hc,he]; exact ht
    have H₁ := ih s (t/2) hs hmid1
    have H₂ := ih (s+(t:ℝ)/2) (t/2) hmid hend1
    rw [dyadicIntervals,chainQuadraticPenalty_append,dyadicIntervals_duration]
    rw [hc]
    have hint := intervalIntegral.integral_add_adjacent_intervals
      (hi s (s+(t:ℝ)/2)) (hi (s+(t:ℝ)/2) (s+t))
    rw [← hint]
    calc
      _ ≤ |chainQuadraticPenalty s (dyadicIntervals α n s (t/2))-
            2*(∫ u in s..s+(t:ℝ)/2, u*α u)|+
          |chainQuadraticPenalty (s+(t:ℝ)/2) (dyadicIntervals α n (s+(t:ℝ)/2) (t/2))-
            2*(∫ u in s+(t:ℝ)/2..s+t, u*α u)| := by
        have hh : ∀ A B C D : ℝ, |A+B-2*(C+D)| ≤ |A-2*C|+|B-2*D| := by
          intro A B C D
          rw [show A+B-2*(C+D)=(A-2*C)+(B-2*D) by ring]
          exact abs_add_le _ _
        exact hh _ _ _ _
      _ ≤ _ := add_le_add (by simpa only [hc] using H₁) (by simpa only [hc,he] using H₂)
      _ = _ := by rw [pow_succ]; ring

end SK.Analytic

end
end

end OAI
