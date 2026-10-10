import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicOperator
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! The logarithmic height conjugation of the radial hyperbolic
operator. The conjugated radial operator is d^2/dt^2 - 1. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaLogLift (f : ℝ → ℂ) (v : ℝ) : ℂ := (v:ℂ)*f (Real.log v)

lemma cubicThetaLogLift_hasDerivAt {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    {v : ℝ} (hv : 0<v) :
    HasDerivAt (cubicThetaLogLift f) (f (Real.log v)+deriv f (Real.log v)) v := by
  have h := Complex.ofRealCLM.hasDerivAt.fun_mul
    ((hf (Real.log v)).hasDerivAt.scomp v (Real.hasDerivAt_log hv.ne'))
  convert h using 1
  · rfl
  · simp only [Function.comp_apply,Complex.ofRealCLM_apply,
      Complex.ofReal_one,one_mul,Complex.real_smul,Complex.ofReal_inv]
    have hn : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
    field_simp

lemma cubicThetaLogLift_second_deriv {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) {v : ℝ} (hv : 0<v) :
    deriv (deriv (cubicThetaLogLift f)) v=
      (v:ℂ)⁻¹*(deriv f (Real.log v)+deriv (deriv f) (Real.log v)) := by
  have he : deriv (cubicThetaLogLift f) =ᶠ[𝓝 v]
      (fun t => f (Real.log t)+deriv f (Real.log t)) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    exact (cubicThetaLogLift_hasDerivAt hf ht).deriv
  rw [he.deriv_eq]
  have h := (((hf (Real.log v)).hasDerivAt.scomp v (Real.hasDerivAt_log hv.ne')).fun_add
    ((hf' (Real.log v)).hasDerivAt.scomp v (Real.hasDerivAt_log hv.ne'))).deriv
  convert h using 1
  · rfl
  · simp only [Complex.real_smul,Complex.ofReal_inv]
    ring

theorem cubicThetaHyperbolicOperator_logLift {f : ℝ → ℂ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (fun _ _ t => cubicThetaLogLift f t) x y v=
      (v:ℂ)*(deriv (deriv f) (Real.log v)-f (Real.log v)) := by
  unfold cubicThetaHyperbolicOperator
  simp only [deriv_const',deriv_const,zero_add]
  rw [cubicThetaLogLift_second_deriv hf hf' hv,(cubicThetaLogLift_hasDerivAt hf hv).deriv]
  have hn : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp
  ring

end CubicFirstMoment

end

end OAI
