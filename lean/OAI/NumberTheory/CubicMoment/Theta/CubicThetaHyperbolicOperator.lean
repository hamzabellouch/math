import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKernelEquation
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace OAI

/-! The upper-half-space differential operator used by the Eisenstein
series, with its horizontal translation and local-equality rules. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaHyperbolicOperator (F : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2*(deriv (deriv (fun t : ℝ => F t y v)) x+
    deriv (deriv (fun t : ℝ => F x t v)) y+
    deriv (deriv (fun t : ℝ => F x y t)) v)-
      (v:ℂ)*deriv (fun t : ℝ => F x y t) v

lemma cubicTheta_deriv_translate (f : ℝ → ℂ) (a : ℝ) :
    deriv (fun t : ℝ => f (t+a))=(fun t : ℝ => deriv f (t+a)) :=
  funext (fun t => deriv_comp_add_const f a t)

lemma cubicThetaHyperbolicOperator_translate (F : ℝ → ℝ → ℝ → ℂ)
    (C : ℂ) (a b x y v : ℝ) :
    cubicThetaHyperbolicOperator (fun u w t => C*F (u+a) (w+b) t) x y v=
      C*cubicThetaHyperbolicOperator F (x+a) (y+b) v := by
  have hx : deriv (deriv (fun t : ℝ => F (t+a) (y+b) v)) x=
      deriv (deriv (fun t : ℝ => F t (y+b) v)) (x+a) := by
    rw [cubicTheta_deriv_translate (fun t : ℝ => F t (y+b) v) a]
    exact deriv_comp_add_const (deriv (fun t : ℝ => F t (y+b) v)) a x
  have hy : deriv (deriv (fun t : ℝ => F (x+a) (t+b) v)) y=
      deriv (deriv (fun t : ℝ => F (x+a) t v)) (y+b) := by
    rw [cubicTheta_deriv_translate (fun t : ℝ => F (x+a) t v) b]
    exact deriv_comp_add_const (deriv (fun t : ℝ => F (x+a) t v)) b y
  unfold cubicThetaHyperbolicOperator
  simp only [deriv_const_mul_field']
  rw [hx,hy]
  ring

lemma cubicThetaHyperbolicOperator_congr {F G : ℝ → ℝ → ℝ → ℂ}
    (hFG : ∀ x y v, 0<v → F x y v=G x y v) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator F x y v=cubicThetaHyperbolicOperator G x y v := by
  have hx : (fun t : ℝ => F t y v)=(fun t : ℝ => G t y v) :=
    funext (fun t => hFG t y v hv)
  have hy : (fun t : ℝ => F x t v)=(fun t : ℝ => G x t v) :=
    funext (fun t => hFG x t v hv)
  have he {u : ℝ} (hu : 0<u) : (fun t : ℝ => F x y t) =ᶠ[𝓝 u] (fun t : ℝ => G x y t) := by
    filter_upwards [eventually_gt_nhds hu] with t ht
    exact hFG x y t ht
  have hd : deriv (fun t : ℝ => F x y t) =ᶠ[𝓝 v] deriv (fun t : ℝ => G x y t) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    exact (he ht).deriv_eq
  unfold cubicThetaHyperbolicOperator
  rw [hx,hy,hd.deriv_eq,(he hv).deriv_eq]

theorem cubicThetaHyperbolicOperator_kernel (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (cubicThetaCartesianKernel s) x y v=
      s*(s-2)*cubicThetaCartesianKernel s x y v :=
  cubicThetaCartesian_eigenvalue s x y hv

end CubicFirstMoment

end

end OAI
