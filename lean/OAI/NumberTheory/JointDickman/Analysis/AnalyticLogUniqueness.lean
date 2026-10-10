import OAI.NumberTheory.JointDickman.Analysis.AnalyticLogBranch
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Uniqueness of normalized analytic logarithms -/
namespace JointDickman
open Set Filter
open scoped Topology

theorem analytic_log_unique {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ s ∈ U, Complex.exp (f s) = Complex.exp (g s))
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) (h₀ : f x₀ = g x₀) : EqOn f g U := by
  have hd : ∀ s ∈ U, deriv f s = deriv g s := by
    intro s hs
    have heq : (fun t => Complex.exp (f t)) =ᶠ[𝓝 s] (fun t => Complex.exp (g t)) := by
      filter_upwards [hU.mem_nhds hs] with t ht
      exact he t ht
    have hh := ((hf s hs).differentiableAt.hasDerivAt.cexp.congr_of_eventuallyEq heq.symm).unique
      (hg s hs).differentiableAt.hasDerivAt.cexp
    rw [he s hs] at hh
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hh
  exact hU.eqOn_of_deriv_eq hc hf.differentiableOn hg.differentiableOn hd hx₀ h₀

end JointDickman

end OAI
