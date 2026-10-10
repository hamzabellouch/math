import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicOperator

namespace OAI

/-! The precise product error when a height-only eigenfunction is
multiplied by a smooth cusp cutoff. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicTheta_vertical_product_second {f g : ℝ → ℂ}
    (hf : ∀ t, 0<t → DifferentiableAt ℝ f t)
    (hg : ∀ t, 0<t → DifferentiableAt ℝ g t)
    (hf' : ∀ t, 0<t → DifferentiableAt ℝ (deriv f) t)
    (hg' : ∀ t, 0<t → DifferentiableAt ℝ (deriv g) t)
    {v : ℝ} (hv : 0<v) :
    deriv (deriv (fun t => f t*g t)) v=
      deriv (deriv f) v*g v+2*deriv f v*deriv g v+f v*deriv (deriv g) v := by
  have he : deriv (fun t => f t*g t) =ᶠ[𝓝 v]
      (fun t => deriv f t*g t+f t*deriv g t) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    have h := ((hf t ht).hasDerivAt.fun_mul (hg t ht).hasDerivAt).deriv
    exact h
  rw [he.deriv_eq]
  have h := (((hf' v hv).hasDerivAt.fun_mul (hg v hv).hasDerivAt).fun_add
    ((hf v hv).hasDerivAt.fun_mul (hg' v hv).hasDerivAt)).deriv
  rw [h]
  ring

theorem cubicThetaHyperbolicOperator_vertical_product {f g : ℝ → ℂ}
    (hf : ∀ t, 0<t → DifferentiableAt ℝ f t)
    (hg : ∀ t, 0<t → DifferentiableAt ℝ g t)
    (hf' : ∀ t, 0<t → DifferentiableAt ℝ (deriv f) t)
    (hg' : ∀ t, 0<t → DifferentiableAt ℝ (deriv g) t)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (fun _ _ t => f t*g t) x y v=
      f v*cubicThetaHyperbolicOperator (fun _ _ t => g t) x y v+
      ((v:ℂ)^2*deriv (deriv f) v-(v:ℂ)*deriv f v)*g v+
      2*(v:ℂ)^2*deriv f v*deriv g v := by
  unfold cubicThetaHyperbolicOperator
  simp only [deriv_const',deriv_const,zero_add]
  rw [cubicTheta_vertical_product_second hf hg hf' hg' hv,
    ((hf v hv).hasDerivAt.fun_mul (hg v hv).hasDerivAt).deriv]
  ring

end CubicFirstMoment

end

end OAI
