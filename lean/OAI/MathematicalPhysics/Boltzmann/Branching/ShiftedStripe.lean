import OAI.MathematicalPhysics.Boltzmann.Branching.StripeCells
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation

namespace OAI

/-! # Centered stripe estimates uniform in spatial phase -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetGeometry

def centeredStripe (p d : ℝ) (a : Bool) (x : ℝ) : ℝ :=
  (stripeLine p a).indicator (fun _ => (1:ℝ)) (x-d)-1/4

theorem centeredStripe_measurable (p d : ℝ) (a : Bool) :
    Measurable (centeredStripe p d a) :=
  (((measurable_const.indicator (stripeLine_measurable p a)).comp
    (measurable_id.sub_const d)).sub_const (1/4))

theorem centeredStripe_bound (p d : ℝ) (a : Bool) (x : ℝ) :
    |centeredStripe p d a x| ≤ 1 := by
  classical
  by_cases hx : x-d ∈ stripeLine p a <;> simp [centeredStripe,hx] <;> norm_num

theorem centeredStripe_periodic (p d : ℝ) (a : Bool) :
    Function.Periodic (centeredStripe p d a) p := by
  intro x
  have h := stripeLine_indicator_periodic p a (x-d)
  simpa only [centeredStripe,add_sub_right_comm] using congrArg (fun z : ℝ => z-1/4) h

theorem centeredStripe_mean {p : ℝ} (hp : 0 < p) (d : ℝ) (a : Bool) :
    (∫ x in 0..p, centeredStripe p d a x) = 0 := by
  let f := (stripeLine p a).indicator (fun _ => (1:ℝ))
  have hm : Measurable (fun x => f (x-d)) :=
    (measurable_const.indicator (stripeLine_measurable p a)).comp (measurable_id.sub_const d)
  have hb (x : ℝ) : |f (x-d)| ≤ 1 := by
    classical
    by_cases hx : x-d ∈ stripeLine p a <;> simp [f,hx]
  have hi := PeriodicAveraging.bounded_intervalIntegrable hm hb 0 p
  change (∫ x in 0..p, f (x-d)-1/4) = 0
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_comp_sub_right,intervalIntegral.integral_const]
  have heq : p-d = (0-d)+p := by ring
  rw [heq,(stripeLine_indicator_periodic p a).intervalIntegral_add_eq (0-d) 0,zero_add,
    stripeLine_integral_period hp a]
  simp only [sub_zero,smul_eq_mul]
  ring

theorem centeredStripe_test_bound {p a b : ℝ} (hp : 0 < p) (hab : a ≤ b)
    (d : ℝ) (σ : Bool) {φ : ℝ → ℝ} (hφ : AbsolutelyContinuousOnInterval φ a b) :
    |∫ x in a..b, φ x*centeredStripe p d σ x| ≤
      (2*p)*(|φ b|+∫ x in a..b, |deriv φ x|) :=
  PeriodicAveraging.test_bound hp hab (centeredStripe_periodic p d σ)
    (centeredStripe_measurable p d σ) (centeredStripe_bound p d σ)
    (centeredStripe_mean hp d σ) hφ

end BoltzmannNonuniqueness.JetGeometry

end

end OAI
