import Mathlib
import OAI.Geometry.WeakHessian.Calculus.NormLpSqIntegral
import OAI.Geometry.WeakHessian.LocalBounds.GammaNatMulLeft

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile153
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.sub (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v A B : X → ℝ}
    (hu : IsLaplacian m u A) (hv : IsLaplacian m v B) :
    IsLaplacian m (fun x => u x-v x) (fun x => A x-B x) := by
  refine ⟨hu.1.sub hfinite hv.1, hu.2.1.sub hv.2.1, ?_⟩
  intro z hz
  rw [integral_congr_ae (gamma_sub_left hfinite hpar hu.1.2.1 hv.1.2.1 hz.2.1),
    integral_sub (integrable_gamma hfinite hu.1 hz) (integrable_gamma hfinite hv.1 hz),
    hu.2.2 z hz,hv.2.2 z hz]
  simp_rw [sub_mul]
  have hiA : Integrable (fun x => A x*z x) m := hu.2.1.integrable_mul hz.1
  have hiB : Integrable (fun x => B x*z x) m := hv.2.1.integrable_mul hz.1
  rw [integral_sub hiA hiB]
  ring

lemma IsLaplacian.positive_resolvent_unique (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {a : ℝ} (ha : 0 < a)
    {u v f : X → ℝ} (hu : IsLaplacian m u (fun x => a*u x-f x))
    (hv : IsLaplacian m v (fun x => a*v x-f x)) : u =ᵐ[m] v := by
  have hD : IsLaplacian m (fun x => u x-v x) (fun x => a*(u x-v x)) := by
    convert hu.sub hfin hpar hv using 1
    funext point
    ring
  let d : X → ℝ := fun x => u x-v x
  have H := hD.2.2 d hD.1
  change (∫ x,gamma m d d x ∂m) = -(∫ x,a*d x*d x ∂m) at H
  have hi : (∫ x,a*d x*d x ∂m) = a*‖hD.1.1.toLp d‖^2 := by
    rw [norm_toLp_sq_eq_integral]
    simp_rw [show ∀ x,a*d x*d x=a*(d x)^2 by intro x; ring]
    exact integral_const_mul _ _
  rw [hi,integral_congr_ae (gamma_self d)] at H
  have hn : 0 ≤ ∫ x,(weakGradient m d x)^2 ∂m := integral_nonneg fun _ => sq_nonneg _
  have hp : a*‖hD.1.1.toLp d‖^2 = 0 := le_antisymm (by linarith only [H,hn])
    (mul_nonneg ha.le (sq_nonneg _))
  have hsq : ‖hD.1.1.toLp d‖^2 = 0 := (mul_eq_zero.mp hp).resolve_left ha.ne'
  have hz : ‖hD.1.1.toLp d‖ = 0 := by nlinarith only [hsq,norm_nonneg (hD.1.1.toLp d)]
  have hz' := norm_eq_zero.mp hz
  filter_upwards [hD.1.1.coeFn_toLp,Lp.coeFn_zero ℝ 2 m] with x hx hy
  rw [hz',hy] at hx
  exact sub_eq_zero.mp hx.symm
end WeakHessian

end
end InlinedFile153

end OAI
