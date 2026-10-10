import OAI.Probability.SLE.Loewner.UnivalentInverseAnalytic
import OAI.Probability.SLE.AngularLaws

namespace OAI

/-! A coarse local growth bound from the proved Bloch omitted-value
estimate. This bound does not use the sharp disk growth input. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma univalent_inverse_derivative_product {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (hi : InjOn f D)
    {a : ℂ} (ha : a∈D) : deriv (invFunOn f D) (f a)*deriv f a=1 := by
  have hg := (univalent_inverse_analyticAt hD hf hi ha).differentiableAt.hasDerivAt
  have h := hg.comp a (hf.differentiableAt (hD.mem_nhds ha)).hasDerivAt
  have he : (invFunOn f D ∘ f) =ᶠ[𝓝 a] id := by
    filter_upwards [hD.mem_nhds ha] with z hz
    exact hi.leftInvOn_invFunOn hz
  exact (he.hasDerivAt_iff.mp h).unique (hasDerivAt_id a)

lemma univalent_coarse_ball_subset_image {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0<r) (hf : DifferentiableOn ℂ f (ball a r)) (hi : InjOn f (ball a r)) :
    ball (f a) (r*‖deriv f a‖/(128*Real.pi)) ⊆ f '' ball a r := by
  intro w hw
  by_contra hn
  have h := univalent_omitted_value_bound_ball hr hf hi w hn
  have hC : 0<128*Real.pi := by positivity
  have hd : ‖f a-w‖<r*‖deriv f a‖/(128*Real.pi) := by
    simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using hw
  have hmul := (lt_div_iff₀ hC).mp hd
  nlinarith

lemma univalent_coarse_local_bound {f : ℂ → ℂ} {a w : ℂ} {r : ℝ}
    (hr : 0<r) (hf : DifferentiableOn ℂ f (ball a r)) (hi : InjOn f (ball a r))
    (hw : w∈ball a (r/(128*Real.pi)^2)) :
    ‖f w-f a‖<r*‖deriv f a‖/(128*Real.pi) := by
  let C : ℝ := 128*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  have ha : a∈ball a r := mem_ball_self hr
  have hfa : 0<‖deriv f a‖ := norm_pos_iff.mpr (univalent_deriv_ne_zero isOpen_ball hf hi ha)
  let R : ℝ := r*‖deriv f a‖/C
  have hR : 0<R := div_pos (mul_pos hr hfa) hC
  let g := invFunOn f (ball a r)
  have hcover : ball (f a) R ⊆ f '' ball a r := univalent_coarse_ball_subset_image hr hf hi
  have hgd : DifferentiableOn ℂ g (ball (f a) R) := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hcover hy
    exact (univalent_inverse_analyticAt isOpen_ball hf hi hz).differentiableAt.differentiableWithinAt
  have hgi : InjOn g (ball (f a) R) := (invFunOn_injOn_image f (ball a r)).mono hcover
  have hbase : g (f a)=a := hi.leftInvOn_invFunOn ha
  have hprod : ‖deriv g (f a)‖*‖deriv f a‖=1 := by
    simpa only [norm_mul,norm_one] using congrArg norm
      (univalent_inverse_derivative_product isOpen_ball hf hi ha)
  have hrad : R*‖deriv g (f a)‖/C=r/C^2 := by
    dsimp [R]
    calc
      r*‖deriv f a‖/C*‖deriv g (f a)‖/C =
          r/C^2*(‖deriv g (f a)‖*‖deriv f a‖) := by ring
      _ = r/C^2 := by rw [hprod,mul_one]
  have hsmall : w∈ball (g (f a)) (R*‖deriv g (f a)‖/C) := by
    rw [hbase,hrad]
    exact hw
  obtain ⟨v,hv,hvw⟩ := univalent_coarse_ball_subset_image hR hgd hgi hsmall
  have hright := (surjOn_image f (ball a r)).rightInvOn_invFunOn (hcover hv)
  change f (g v)=v at hright
  rw [hvw] at hright
  rw [hright]
  simpa only [mem_ball,dist_eq_norm] using hv

end SLEExactGauge

end

end OAI
