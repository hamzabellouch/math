import OAI.Analysis.CircleDomains.Sobolev.NormalizedArgumentDifferential
import OAI.Analysis.CircleDomains.Topology.UnorientedCircleGreen
import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization

namespace OAI

/-! The normalized angular form has integral one on a positively
traversed round circle. Both the form and its tangent are actual derivatives. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def centeredArgument (c z : ℂ) : UnitAddCircle := normalizedArgument (z-c)

lemma smoothCircleOn_centeredArgument (c : ℂ) :
    SmoothCircleOn (centeredArgument c) {z | z ≠ c} := by
  intro z hz a ha
  exact (smoothCircleOn_normalizedArgument (z-c) (sub_ne_zero.mpr hz) a ha).comp (f := fun w : ℂ => w-c) z
    (contDiffAt_id.sub contDiffAt_const)

lemma circleFDeriv_centeredArgument (c : ℂ) {z : ℂ} (hz : z ≠ c) (v : ℂ) :
    circleFDeriv (centeredArgument c) z v = (v/(z-c)).im/(2*Real.pi) := by
  have hh := circleFDeriv_comp (f := fun w : ℂ => w-c) (isOpen_ne_fun continuous_id continuous_const)
    smoothCircleOn_normalizedArgument
    (differentiableAt_id.sub (differentiableAt_const c)) (sub_ne_zero.mpr hz)
  change circleFDeriv (normalizedArgument ∘ (fun w : ℂ => w-c)) z v = _
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply, fderiv_sub_const, fderiv_fun_id,
    ContinuousLinearMap.id_apply]
  exact circleFDeriv_normalizedArgument (sub_ne_zero.mpr hz) v

lemma circleFormIntegral_eq_covector (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle) (γ : ℝ → ℂ) :
    circleFormIntegral φ u γ =
      ∫ t in (0 : ℝ)..1, φ (γ t) * circleFDeriv u (γ t) (deriv γ t) := by
  unfold circleFormIntegral planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [Pi.mul_apply]
  conv_rhs => rw [complexCovector_apply]
  ring

lemma unitCircleParam_hasDerivAt_centered (c : ℂ) (r t : ℝ) :
    HasDerivAt (unitCircleParam c r)
      ((unitCircleParam c r t-c) * Complex.I * (2*Real.pi)) t := by
  have he : unitCircleParam c r = fun s => c + unitCircleParam 0 r s := by
    funext s
    simp [unitCircleParam, circleMap]
  rw [he]
  simpa only [unitCircleParam, circleMap, zero_add, add_sub_cancel_left] using
    (unitCircleParam_hasDerivAt r t).const_add c

lemma unitCircleParam_ne_center (c : ℂ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    unitCircleParam c r t ≠ c := circleMap_ne_center hr.ne'

lemma centeredArgument_round_integral (c : ℂ) {r : ℝ} (hr : 0 < r) :
    circleFormIntegral (fun _ => 1) (centeredArgument c) (unitCircleParam c r) = 1 := by
  rw [circleFormIntegral_eq_covector]
  have he (t : ℝ) : (1 : ℝ) * circleFDeriv (centeredArgument c)
      (unitCircleParam c r t) (deriv (unitCircleParam c r) t) = 1 := by
    rw [one_mul, circleFDeriv_centeredArgument c (unitCircleParam_ne_center c hr t),
      (unitCircleParam_hasDerivAt_centered c r t).deriv]
    have hn : unitCircleParam c r t-c ≠ 0 := sub_ne_zero.mpr (unitCircleParam_ne_center c hr t)
    rw [mul_assoc, mul_div_cancel_left₀ _ hn]
    simp [Complex.mul_im]
  simp only [he, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

end CircleDomainRigidity

end

end OAI
