import OAI.NumberTheory.JointDickman.Amplification.DiscardedRegionBound

namespace OAI

/-! # Local replacement errors controlled by endpoint square integrals -/

namespace JointDickman
open MeasureTheory

theorem weighted_interval_energy_error {a b E : ℝ} {F G H K : ℝ → ℂ}
    (hab : a ≤ b) (hE : 0 ≤ E) (hF : Continuous F) (hG : Continuous G)
    (hH : Continuous H) (hK : Continuous K)
    (he : ∀ x ∈ Set.Icc a b, ‖H x-K x‖ ≤ E) :
    ‖(∫ x in a..b, F x*G x*H x)-(∫ x in a..b, F x*G x*K x)‖ ≤
      E/2*((∫ x in a..b, ‖F x‖^2)+(∫ x in a..b, ‖G x‖^2)) := by
  rw [← intervalIntegral.integral_sub (f := fun x => F x*G x*H x)
    (g := fun x => F x*G x*K x)
    (((hF.mul hG).mul hH).intervalIntegrable a b)
    (((hF.mul hG).mul hK).intervalIntegrable a b)]
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      ‖F x*G x*H x-F x*G x*K x‖ ≤ E/2*(‖F x‖^2+‖G x‖^2) := by
    rw [← mul_sub,norm_mul,norm_mul]
    have hy : ‖F x‖*‖G x‖ ≤ (‖F x‖^2+‖G x‖^2)/2 := by
      nlinarith [sq_nonneg (‖F x‖-‖G x‖)]
    calc
      _ ≤ (‖F x‖*‖G x‖)*E := mul_le_mul_of_nonneg_left (he x hx) (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hy hE]
  have hi : IntervalIntegrable (fun x => E/2*(‖F x‖^2+‖G x‖^2)) volume a b :=
    (continuous_const.mul ((hF.norm.pow 2).add (hG.norm.pow 2))).intervalIntegrable a b
  calc
    _ ≤ ∫ x in a..b, E/2*(‖F x‖^2+‖G x‖^2) :=
      intervalIntegral.norm_integral_le_of_norm_le hab
        (Filter.Eventually.of_forall (fun x hx => hbound x ⟨hx.1.le,hx.2⟩)) hi
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (f := fun x => ‖F x‖^2) (g := fun x => ‖G x‖^2)
        ((hF.norm.pow 2).intervalIntegrable a b) ((hG.norm.pow 2).intervalIntegrable a b)]

end JointDickman

end OAI
