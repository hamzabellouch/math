import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularContour
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowGaugedEquation

namespace OAI

/-! Chain rules and the actual gauged equation along a complex contour. -/

open Filter Topology
namespace DefocusingNLS

theorem analyticOnNhd_slowGauge (M : ℕ) :
    AnalyticOnNhd ℂ (slowGauge M) Complex.slitPlane := by
  apply DifferentiableOn.analyticOnNhd _ Complex.isOpen_slitPlane
  intro x hx
  exact (hasDerivAt_slowGauge M x hx).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_gaugedSlowSolution (q : ℂ) (M : ℕ) (hq : -1 < q.re) :
    AnalyticOnNhd ℂ (gaugedSlowSolution q M) Complex.slitPlane :=
  (analyticOnNhd_slowGauge M).mul
    (analyticOnNhd_regularizedSlowSolution_slit q (M+1) hq)

/-- The first two derivatives along a twice differentiable contour. -/
theorem analytic_path_derivatives (F : ℂ → ℂ) (γ g : ℝ → ℂ) (s : ℝ)
    (hF : AnalyticAt ℂ F (γ s)) (hγ : ∀ t, HasDerivAt γ (g t) t)
    (g' : ℂ) (hg : HasDerivAt g g' s) :
    deriv (fun t => F (γ t)) s = g s*deriv F (γ s) ∧
      deriv (deriv (fun t => F (γ t))) s =
        g'*deriv F (γ s)+(g s)^2*deriv (deriv F) (γ s) := by
  have h₁ : ∀ t, AnalyticAt ℂ F (γ t) →
      HasDerivAt (fun r => F (γ r)) (g t*deriv F (γ t)) t := by
    intro t ht
    simpa only [Function.comp_def,smul_eq_mul] using
      ht.differentiableAt.hasDerivAt.scomp t (hγ t)
  have heq : deriv (fun t => F (γ t)) =ᶠ[𝓝 s]
      (fun t => g t*deriv F (γ t)) := by
    filter_upwards [(hγ s).continuousAt.tendsto.eventually hF.eventually_analyticAt] with t ht
    exact (h₁ t ht).deriv
  have h₂ : HasDerivAt (fun t => deriv F (γ t))
      (g s*deriv (deriv F) (γ s)) s := by
    simpa only [Function.comp_def,smul_eq_mul] using
      hF.deriv.differentiableAt.hasDerivAt.scomp s (hγ s)
  refine ⟨(h₁ s hF).deriv,?_⟩
  have h := ((hg.mul h₂).congr_of_eventuallyEq heq).deriv
  rw [h]
  ring

/-- The second chain rule as an actual derivative, for use in the flux derivative. -/
theorem analytic_path_hasDerivAt_deriv (F : ℂ → ℂ) (γ g : ℝ → ℂ) (s : ℝ)
    (hF : AnalyticAt ℂ F (γ s)) (hγ : ∀ t, HasDerivAt γ (g t) t)
    (g' : ℂ) (hg : HasDerivAt g g' s) :
    HasDerivAt (deriv (fun t => F (γ t)))
      (g'*deriv F (γ s)+(g s)^2*deriv (deriv F) (γ s)) s := by
  have heq : deriv (fun t => F (γ t)) =ᶠ[𝓝 s]
      (fun t => g t*deriv F (γ t)) := by
    filter_upwards [(hγ s).continuousAt.tendsto.eventually hF.eventually_analyticAt] with t ht
    simpa only [Function.comp_def,smul_eq_mul] using
      (ht.differentiableAt.hasDerivAt.scomp t (hγ t)).deriv
  have h₂ : HasDerivAt (fun t => deriv F (γ t))
      (g s*deriv (deriv F) (γ s)) s := by
    simpa only [Function.comp_def,smul_eq_mul] using
      hF.deriv.differentiableAt.hasDerivAt.scomp s (hγ s)
  convert! (hg.mul h₂).congr_of_eventuallyEq heq using 1
  ring

/-- The Kummer gauge equation after changing to an arc-length contour. -/
theorem gaugedSlowSolution_path_equation (q : ℂ) (M : ℕ) (γ g : ℝ → ℂ)
    (s : ℝ) (C : ℂ) (hq : -1 < q.re)
    (hx : 0 ≤ (γ s).re) (hx0 : γ s ≠ 0) (hg0 : g s ≠ 0)
    (hγ : ∀ t, HasDerivAt γ (g t) t) (hg : HasDerivAt g (-C*g s) s) :
    -(γ s/(g s)^2)*deriv (deriv (fun t => gaugedSlowSolution q M (γ t))) s-
      (1/g s+C*(γ s/(g s)^2))*deriv (fun t => gaugedSlowSolution q M (γ t)) s+
      (γ s/4+(M : ℂ)^2/(4*γ s))*gaugedSlowSolution q M (γ s) =
      (((M : ℂ)+1)/2-q)*gaugedSlowSolution q M (γ s) := by
  have hs : γ s ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    rcases hx.eq_or_lt with he | he
    · exact Or.inr (fun hi => hx0 (Complex.ext he.symm hi))
    · exact Or.inl he
  obtain ⟨h₁,h₂⟩ := analytic_path_derivatives (gaugedSlowSolution q M) γ g s
    (analyticOnNhd_gaugedSlowSolution q M hq (γ s) hs) hγ (-C*g s) hg
  rw [h₁,h₂]
  have hODE := gaugedSlowSolution_equation q M (γ s) hq hx hx0
  convert! hODE using 1
  field_simp [hg0]
  ring

end DefocusingNLS

end OAI
