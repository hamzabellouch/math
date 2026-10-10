import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCutoff
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantSpectral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaVerticalProduct

namespace OAI

/-! The concrete compactly supported forcing term introduced by removing
the constant Fourier coefficient above the cusp cutoff. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaCuspForcing (s : ℂ) (v : ℝ) : ℂ :=
  ((v:ℂ)^2*deriv (deriv cubicThetaCuspCutoff) v-(v:ℂ)*deriv cubicThetaCuspCutoff v)*
    cubicThetaEisensteinConstantMode v s+
  2*(v:ℂ)^2*deriv cubicThetaCuspCutoff v*
    deriv (fun t => cubicThetaEisensteinConstantMode t s) v

theorem cubicThetaCutoffConstantMode_equation {s : ℂ} (hs : 1<s.re)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun _ _ t => cubicThetaCuspCutoff t*cubicThetaEisensteinConstantMode t s) x y v=
      s*(s-2)*(cubicThetaCuspCutoff v*cubicThetaEisensteinConstantMode v s)+
        cubicThetaCuspForcing s v := by
  have hc : Differentiable ℝ cubicThetaCuspCutoff :=
    cubicThetaCuspCutoff_smooth.differentiable (by simp)
  have hc' : Differentiable ℝ (deriv cubicThetaCuspCutoff) :=
    (cubicThetaCuspCutoff_smooth.of_le (by simp : (2:ℕ∞ω) ≤ ∞)).differentiable_deriv_two
  rw [cubicThetaHyperbolicOperator_vertical_product (fun t _ => hc t)
    (fun _ ht => (cubicThetaEisensteinConstantMode_analytic hs ht).differentiableAt)
    (fun t _ => hc' t)
    (fun _ ht => (cubicThetaEisensteinConstantMode_analytic hs ht).deriv.differentiableAt) x y hv,
    cubicThetaEisensteinConstantMode_eigenvalue hs x y hv]
  unfold cubicThetaCuspForcing
  ring

lemma cubicThetaCuspForcing_zero (s : ℂ) {v : ℝ} (hv : v<1 ∨ 2<v) :
    cubicThetaCuspForcing s v=0 := by
  obtain ⟨h₁,h₂⟩ := cubicThetaCuspCutoff_derivatives_zero hv
  simp [cubicThetaCuspForcing,h₁,h₂]

theorem cubicThetaCuspForcing_compact (s : ℂ) : HasCompactSupport (cubicThetaCuspForcing s) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra h
  have he : v<1 ∨ 2<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using h
  exact hv (cubicThetaCuspForcing_zero s he)

end CubicFirstMoment

end

end OAI
