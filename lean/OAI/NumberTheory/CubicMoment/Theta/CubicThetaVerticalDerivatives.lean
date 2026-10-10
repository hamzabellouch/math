import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuadraticDerivatives

namespace OAI

/-! Vertical derivatives of the height-weighted hyperbolic kernel. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaVerticalKernel (s : ℂ) (b v : ℝ) : ℂ :=
  (v:ℂ)^s*cubicThetaQuadraticPower (-s) b v

def cubicThetaVerticalFirst (s : ℂ) (b v : ℝ) : ℂ :=
  s*(v:ℂ)^(s-1)*cubicThetaQuadraticPower (-s) b v+
    (v:ℂ)^s*cubicThetaQuadraticFirst (-s) b v

def cubicThetaVerticalSecond (s : ℂ) (b v : ℝ) : ℂ :=
  s*(s-1)*(v:ℂ)^(s-2)*cubicThetaQuadraticPower (-s) b v+
    2*s*(v:ℂ)^(s-1)*cubicThetaQuadraticFirst (-s) b v+
    (v:ℂ)^s*cubicThetaQuadraticSecond (-s) b v

lemma cubicThetaHeightPower_hasDerivAt (s : ℂ) {v : ℝ} (hv : 0<v) :
    HasDerivAt (fun t : ℝ => (t:ℂ)^s) (s*(v:ℂ)^(s-1)) v :=
  (Complex.hasStrictDerivAt_cpow_const (c:=s)
    (Complex.ofReal_mem_slitPlane.mpr hv)).hasDerivAt.comp_ofReal

lemma cubicThetaVertical_hasDerivAt (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    HasDerivAt (cubicThetaVerticalKernel s b) (cubicThetaVerticalFirst s b v) v :=
  (cubicThetaHeightPower_hasDerivAt s hv).mul
    (cubicThetaQuadratic_hasDerivAt (-s) b v (add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) hb))

lemma cubicThetaVerticalFirst_hasDerivAt (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    HasDerivAt (cubicThetaVerticalFirst s b) (cubicThetaVerticalSecond s b v) v := by
  have hR : 0<v^2+b := add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) hb
  have h₁ := ((cubicThetaHeightPower_hasDerivAt (s-1) hv).const_mul s).mul
    (cubicThetaQuadratic_hasDerivAt (-s) b v hR)
  have h₂ := (cubicThetaHeightPower_hasDerivAt s hv).mul
    (cubicThetaQuadraticFirst_hasDerivAt (-s) b v hR)
  convert h₁.add h₂ using 1
  · rfl
  · unfold cubicThetaVerticalSecond
    rw [show s-1-1=s-2 by ring]
    ring

lemma cubicThetaVertical_deriv (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    deriv (cubicThetaVerticalKernel s b) v=cubicThetaVerticalFirst s b v :=
  (cubicThetaVertical_hasDerivAt s hb hv).deriv

theorem cubicThetaVertical_second_deriv (s : ℂ) {b v : ℝ} (hb : 0 ≤ b) (hv : 0<v) :
    deriv (deriv (cubicThetaVerticalKernel s b)) v=cubicThetaVerticalSecond s b v := by
  have he : deriv (cubicThetaVerticalKernel s b) =ᶠ[𝓝 v] cubicThetaVerticalFirst s b := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    exact cubicThetaVertical_deriv s hb ht
  exact ((cubicThetaVerticalFirst_hasDerivAt s hb hv).congr_of_eventuallyEq he).deriv

end CubicFirstMoment

end

end OAI
