import OAI.Analysis.CircleDomains.Reflection.SmoothBeltramiDistortion

namespace OAI

/-! Exact cancellation of the Beltrami coefficient when a smooth function
is pulled back by the inverse of the smooth comparison map. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma smooth_beltrami_pullback_cancellation (P : ℂ ≃ₜ ℂ)
    (hP : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hPi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    (μ : ℂ → ℂ) (he : ∀z,partialBar P.symm z=μ z*partialZ P.symm z)
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f (P z)) :
    partialBar (f ∘ P) z=
      (partialBar f (P z)-μ (P z)*partialZ f (P z))*star (partialZ P z) := by
  have hd := hP.differentiable (by simp)
  have hdi := hPi.differentiable (by simp)
  have hn := smooth_homeomorph_partialZ_ne_zero P.symm hdi hd μ he
  have hi := inverse_partialBar P.symm hdi hd μ he hn z
  change partialBar P z= -μ (P z)*star (partialZ P z) at hi
  rw [(partials_comp hf (hd z)).2,hi]
  ring

lemma smooth_beltrami_pullback_cancellation_bound (P : ℂ ≃ₜ ℂ)
    (hP : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hPi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    (μ : ℂ → ℂ) (he : ∀z,partialBar P.symm z=μ z*partialZ P.symm z)
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f (P z)) :
    ‖partialBar (f ∘ P) z‖=
      ‖partialBar f (P z)-μ (P z)*partialZ f (P z)‖*‖partialZ P z‖ := by
  rw [smooth_beltrami_pullback_cancellation P hP hPi μ he hf,norm_mul,norm_star]

end CircleDomainRigidity

end

end OAI
