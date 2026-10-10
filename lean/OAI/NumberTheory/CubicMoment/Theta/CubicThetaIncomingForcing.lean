import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspForcing

namespace OAI

/-! The incoming height term gives an entire family of compact annular
forcing terms. This is the scalar term to be assembled in the arithmetic
cusps before applying the continued global resolvent. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaIncomingForcing (s : ℂ) (v : ℝ) : ℂ :=
  ((v:ℂ)^2*deriv (deriv cubicThetaCuspCutoff) v-(v:ℂ)*deriv cubicThetaCuspCutoff v)*
      (v:ℂ)^s+
    2*(v:ℂ)^2*deriv cubicThetaCuspCutoff v*s*(v:ℂ)^(s-1)

theorem cubicThetaCutoffIncoming_equation (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun _ _ t => cubicThetaCuspCutoff t*(t:ℂ)^s) x y v=
      s*(s-2)*(cubicThetaCuspCutoff v*(v:ℂ)^s)+cubicThetaIncomingForcing s v := by
  have hc : Differentiable ℝ cubicThetaCuspCutoff :=
    cubicThetaCuspCutoff_smooth.differentiable (by simp)
  have hc' : Differentiable ℝ (deriv cubicThetaCuspCutoff) :=
    (cubicThetaCuspCutoff_smooth.of_le (by simp : (2:ℕ∞ω)≤∞)).differentiable_deriv_two
  rw [cubicThetaHyperbolicOperator_vertical_product (fun t _ => hc t)
    (fun _ ht => (cubicThetaHeightPower_analytic s ht).differentiableAt)
    (fun t _ => hc' t)
    (fun _ ht => (cubicThetaHeightPower_analytic s ht).deriv.differentiableAt) x y hv,
    cubicThetaHyperbolicOperator_height s x y hv,cubicThetaHeightPower_deriv s hv]
  unfold cubicThetaIncomingForcing
  ring

lemma cubicThetaIncomingForcing_zero (s : ℂ) {v : ℝ} (hv : v<1 ∨ 2<v) :
    cubicThetaIncomingForcing s v=0 := by
  obtain ⟨h₁,h₂⟩ := cubicThetaCuspCutoff_derivatives_zero hv
  simp [cubicThetaIncomingForcing,h₁,h₂]

lemma cubicThetaIncomingForcing_compact (s : ℂ) :
    HasCompactSupport (cubicThetaIncomingForcing s) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra h
  have he : v<1 ∨ 2<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using h
  exact hv (cubicThetaIncomingForcing_zero s he)

lemma cubicThetaIncomingForcing_analytic (v : ℝ) (s : ℂ) :
    AnalyticAt ℂ (fun z => cubicThetaIncomingForcing z v) s := by
  by_cases hv : v<1
  · have he : (fun z => cubicThetaIncomingForcing z v)=(fun _ => 0) := by
      funext z
      exact cubicThetaIncomingForcing_zero z (Or.inl hv)
    rw [he]
    exact analyticAt_const
  · have hv0 : 0<v := lt_of_lt_of_le zero_lt_one (le_of_not_gt hv)
    let _ : NeZero (v:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hv0.ne'⟩
    have hp (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => (v:ℂ)^w) z :=
      (differentiable_const_cpow_of_neZero (v:ℂ)).analyticAt z
    have hshift : AnalyticAt ℂ (fun z : ℂ => (v:ℂ)^(z-1)) s :=
      (hp (s-1)).comp (f:=fun z : ℂ => z-1) (x:=s) (analyticAt_id.sub analyticAt_const)
    exact (analyticAt_const.mul (hp s)).add
      ((analyticAt_const.mul analyticAt_id).mul hshift)

end CubicFirstMoment

end

end OAI
