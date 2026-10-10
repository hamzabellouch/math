import OAI.Analysis.CircleDomains.Selection.PrincipalExteriorGerm
import Mathlib.Analysis.Complex.MeanValue

namespace OAI

/-! The exact angular mean of the derivative of a principal exterior
map. Inversion turns the derivative into a holomorphic disk function
with value one at its center. No area inequality is used. -/
open Set Filter Function Metric Asymptotics Bornology Real
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma circleAverage_comp_inv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (r : ℝ) :
    circleAverage (fun z => f z⁻¹) 0 r = circleAverage f 0 r⁻¹ := by
  rw [circleAverage_eq_circleAverage_zero_one,
    circleAverage_eq_circleAverage_zero_one (f := f)]
  simp only [add_zero, mul_inv_rev, Complex.ofReal_inv]
  have he : (fun z : ℂ => f (z⁻¹ * (r : ℂ)⁻¹)) =
      (fun z : ℂ => f ((r : ℂ)⁻¹ * z)) ∘ (fun z => z⁻¹) := by
    funext z
    simp only [comp_apply, mul_comm]
  rw [he]
  simpa only [Function.comp_def] using
    (circleAverage_zero_one_congr_inv (f := fun z : ℂ => f ((r : ℂ)⁻¹ * z)))

lemma invertedPrincipalRemainder_analyticOnNhd {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) :
    AnalyticOnNhd ℂ (invertedPrincipalRemainder F) (ball 0 R⁻¹) := by
  have hfar : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
    exact (hF z hz).differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    exact invertedPrincipalRemainder_analytic hfar ht
  · have hwR : R < ‖w⁻¹‖ := by
      rw [norm_inv]
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hwlt : ‖w‖ < R⁻¹ := by simpa only [mem_ball, dist_zero_right] using hw
      exact (lt_inv_comm₀ hR hwpos).mpr hwlt
    have ha := hF.analyticAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hwR)
    have hi : AnalyticAt ℂ (fun z : ℂ => z⁻¹) w := analyticAt_inv hw0
    apply ((ha.comp hi).sub hi).congr
    filter_upwards [isOpen_ne.mem_nhds hw0] with z hz
    exact (Function.update_of_ne hz _ _).symm

def invertedPrincipalDerivative (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  1 - w^2 * deriv (invertedPrincipalRemainder F) w

lemma invertedPrincipalDerivative_zero (F : ℂ → ℂ) :
    invertedPrincipalDerivative F 0 = 1 := by simp [invertedPrincipalDerivative]

lemma invertedPrincipalDerivative_eq {F : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0)
    (hF : DifferentiableAt ℂ F w⁻¹) :
    invertedPrincipalDerivative F w = deriv F w⁻¹ := by
  have hi : HasDerivAt (fun z : ℂ => z⁻¹) (-w⁻¹^2) w := by
    simpa only [inv_pow] using (hasDerivAt_inv hw)
  have hu := (hF.hasDerivAt.comp w hi).sub hi
  have hue : HasDerivAt (invertedPrincipalRemainder F)
      (deriv F w⁻¹ * (-w⁻¹^2) - (-w⁻¹^2)) w := by
    apply hu.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hw] with z hz
    exact Function.update_of_ne hz _ _
  rw [invertedPrincipalDerivative, hue.deriv]
  field_simp
  ring

lemma exterior_derivative_circleAverage {F : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) (hr : R < r) :
    circleAverage (deriv F) 0 r = 1 := by
  have hrp : 0 < r := hR.trans hr
  have hu := invertedPrincipalRemainder_analyticOnNhd hR hF ht
  have hv : AnalyticOnNhd ℂ (invertedPrincipalDerivative F) (ball 0 R⁻¹) := by
    intro w hw
    exact analyticAt_const.sub ((analyticAt_id.pow 2).mul
      ((hu w hw).deriv))
  have hsub : closedBall (0 : ℂ) r⁻¹ ⊆ ball 0 R⁻¹ := by
    intro w hw
    have hh : r⁻¹ < R⁻¹ := inv_lt_inv₀ hrp hR |>.mpr hr
    exact (show dist w 0 ≤ r⁻¹ from hw).trans_lt hh
  have hav : circleAverage (invertedPrincipalDerivative F) 0 r⁻¹ = 1 := by
    rw [← invertedPrincipalDerivative_zero F]
    apply circleAverage_of_differentiable_on_off_countable (s := ∅)
      countable_empty
    · simpa only [abs_of_pos (inv_pos.mpr hrp)] using
        (hv.continuousOn.mono hsub)
    · intro w hw
      exact (hv w (hsub (ball_subset_closedBall (by
        simpa only [sdiff_empty, abs_of_pos (inv_pos.mpr hrp)] using hw)))).differentiableAt
  rw [← circleAverage_comp_inv] at hav
  refine (circleAverage_congr_sphere (fun z hz => ?_)).trans hav
  have hzn : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right, abs_of_pos hrp] using hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzn]; exact hrp.ne')
  have hdz : DifferentiableAt ℂ F z⁻¹⁻¹ := by
    simpa only [inv_inv] using ((hF z (by simpa only [mem_ofPred_eq, hzn] using hr)).differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (by simpa only [mem_ofPred_eq, hzn] using hr)))
  simpa only [inv_inv] using (invertedPrincipalDerivative_eq (inv_ne_zero hz0) hdz).symm

end CircleDomainRigidity

end

end OAI
