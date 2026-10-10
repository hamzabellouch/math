import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicOperator

namespace OAI

/-! The leading cusp-height term satisfies the same eigenvalue
equation as the nonzero Eisenstein summands. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaHeightPower_deriv (s : ℂ) {v : ℝ} (hv : 0<v) :
    deriv (fun t : ℝ => (t:ℂ)^s) v=s*(v:ℂ)^(s-1) :=
  (cubicThetaHeightPower_hasDerivAt s hv).deriv

lemma cubicThetaHeightPower_second_deriv (s : ℂ) {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t : ℝ => (t:ℂ)^s)) v=s*(s-1)*(v:ℂ)^(s-2) := by
  have he : deriv (fun t : ℝ => (t:ℂ)^s) =ᶠ[𝓝 v]
      (fun t : ℝ => s*(t:ℂ)^(s-1)) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    exact cubicThetaHeightPower_deriv s ht
  have hd := (cubicThetaHeightPower_hasDerivAt (s-1) hv).const_mul s
  have hd' := (hd.congr_of_eventuallyEq he).deriv
  simpa only [show s-1-1=s-2 by ring,mul_assoc] using hd'

theorem cubicThetaHyperbolicOperator_height (s : ℂ) (x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (fun _ _ t => (t:ℂ)^s) x y v=
      s*(s-2)*(v:ℂ)^s := by
  have hn := Complex.ofReal_ne_zero.mpr hv.ne'
  unfold cubicThetaHyperbolicOperator
  simp only [deriv_const',deriv_const,zero_add]
  rw [cubicThetaHeightPower_second_deriv s hv,cubicThetaHeightPower_deriv s hv,
    Complex.cpow_sub s 2 hn,Complex.cpow_sub s 1 hn]
  norm_num only [Complex.cpow_one,Complex.cpow_ofNat]
  field_simp
  ring

end CubicFirstMoment

end

end OAI
