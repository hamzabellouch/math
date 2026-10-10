import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowContinuation
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! Real coordinate derivatives of the quadratic powers occurring in
the hyperbolic Eisenstein kernel. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

private lemma real_cpow_hasDerivAt {f : ℝ → ℝ} {x f' : ℝ}
    (hf : HasDerivAt f f' x) (hp : 0<f x) (r : ℂ) :
    HasDerivAt (fun t : ℝ => (f t:ℂ)^r)
      (r*(f x:ℂ)^(r-1)*(f':ℂ)) x := by
  have h := (Complex.hasStrictDerivAt_cpow_const (c:=r)
    (Complex.ofReal_mem_slitPlane.mpr hp)).hasDerivAt.scomp x hf.ofReal_comp
  change HasDerivAt (fun t : ℝ => (f t:ℂ)^r)
    ((f':ℂ)*(r*(f x:ℂ)^(r-1))) x at h
  convert h using 1
  ring

def cubicThetaQuadraticPower (r : ℂ) (b t : ℝ) : ℂ := ((t^2+b:ℝ):ℂ)^r

def cubicThetaQuadraticFirst (r : ℂ) (b t : ℝ) : ℂ :=
  2*r*(t:ℂ)*cubicThetaQuadraticPower (r-1) b t

def cubicThetaQuadraticSecond (r : ℂ) (b t : ℝ) : ℂ :=
  2*r*cubicThetaQuadraticPower (r-1) b t+
    4*r*(r-1)*(t:ℂ)^2*cubicThetaQuadraticPower (r-2) b t

lemma cubicThetaQuadratic_hasDerivAt (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    HasDerivAt (cubicThetaQuadraticPower r b) (cubicThetaQuadraticFirst r b x) x := by
  have hq : HasDerivAt (fun t : ℝ => t^2+b) (2*x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const b using 1 <;> norm_num
  have h := real_cpow_hasDerivAt hq hx r
  unfold cubicThetaQuadraticFirst cubicThetaQuadraticPower
  convert h using 1
  push_cast
  ring

lemma cubicThetaQuadraticFirst_hasDerivAt (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    HasDerivAt (cubicThetaQuadraticFirst r b) (cubicThetaQuadraticSecond r b x) x := by
  have h := ((hasDerivAt_id x).ofReal_comp.mul
    (cubicThetaQuadratic_hasDerivAt (r-1) b x hx)).const_mul (2*r)
  convert h using 1
  · funext t
    dsimp only [cubicThetaQuadraticFirst,Pi.mul_apply,id_eq]
    ring
  · dsimp only [cubicThetaQuadraticFirst,cubicThetaQuadraticSecond,id_eq]
    rw [show r-1-1=r-2 by ring]
    push_cast
    ring

lemma cubicThetaQuadratic_deriv (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    deriv (cubicThetaQuadraticPower r b) x=cubicThetaQuadraticFirst r b x :=
  (cubicThetaQuadratic_hasDerivAt r b x hx).deriv

theorem cubicThetaQuadratic_second_deriv (r : ℂ) (b x : ℝ) (hx : 0<x^2+b) :
    deriv (deriv (cubicThetaQuadraticPower r b)) x=cubicThetaQuadraticSecond r b x := by
  have hpos : ∀ᶠ t : ℝ in 𝓝 x, 0<t^2+b := by
    exact (isOpen_lt continuous_const ((continuous_pow 2).add_const b)).mem_nhds hx
  have he : deriv (cubicThetaQuadraticPower r b) =ᶠ[𝓝 x] cubicThetaQuadraticFirst r b := by
    filter_upwards [hpos] with t ht
    exact cubicThetaQuadratic_deriv r b t ht
  exact ((cubicThetaQuadraticFirst_hasDerivAt r b x hx).congr_of_eventuallyEq he).deriv

end CubicFirstMoment

end

end OAI
