import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace OAI

/-! # Analytic logarithms on the zero-free contour domains -/
namespace JointDickman
open Filter Set
open scoped Topology

theorem analyticAt_of_continuousAt_exp {f : ℂ → ℂ} {x : ℂ}
    (hf : ContinuousAt f x) (he : AnalyticAt ℂ (fun y => Complex.exp (f y)) x) :
    AnalyticAt ℂ f x := by
  have hE : AnalyticAt ℂ Complex.exp (f x) := analyticAt_cexp
  have hd : deriv Complex.exp (f x) ≠ 0 := by
    rw [Complex.deriv_exp]
    exact Complex.exp_ne_zero _
  let r := hE.hasStrictDerivAt.localInverse _ _ _ hd
  have hr : AnalyticAt ℂ r (Complex.exp (f x)) := hE.analyticAt_localInverse hd
  have hi : (fun y => r (Complex.exp (f y))) =ᶠ[𝓝 x] f :=
    hf.eventually (hE.hasStrictDerivAt.eventually_left_inverse hd)
  have har : AnalyticAt ℂ (fun y => r (Complex.exp (f y))) x :=
    AnalyticAt.comp (f := fun y => Complex.exp (f y)) hr he
  exact har.congr hi

theorem exists_analytic_log_on {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∀ x ∈ U, g x ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ ∀ x ∈ U, Complex.exp (f x) = g x := by
  obtain ⟨f,hf,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hg.continuousOn
    (by rintro ⟨x,hx,heq⟩; exact hne x hx heq)
  refine ⟨f,fun x hx => ?_,he⟩
  apply analyticAt_of_continuousAt_exp (hf.continuousAt (hUo.mem_nhds hx))
  apply (hg x hx).congr
  exact (Filter.eventuallyEq_of_mem (hUo.mem_nhds hx) (fun y hy => he hy)).symm

theorem exists_normalized_analytic_log_on {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) {x₀ : ℂ} (hx₀ : x₀ ∈ U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∀ x ∈ U, g x ≠ 0)
    (hg₀ : g x₀ = 1) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ f x₀ = 0 ∧
      ∀ x ∈ U, Complex.exp (f x) = g x := by
  obtain ⟨f,hf,he⟩ := exists_analytic_log_on hUc hUo hg hne
  refine ⟨fun x => f x-f x₀,fun x hx => (hf x hx).sub analyticAt_const,sub_self _,?_⟩
  intro x hx
  rw [Complex.exp_sub,he x hx,he x₀ hx₀,hg₀,div_one]

theorem normalized_log_eq_principal_near {f g : ℂ → ℂ} {x : ℂ}
    (hf : ContinuousAt f x) (hf₀ : f x = 0)
    (he : (fun y => Complex.exp (f y)) =ᶠ[𝓝 x] g) :
    f =ᶠ[𝓝 x] (fun y => Complex.log (g y)) := by
  have him : Tendsto (fun y => (f y).im) (𝓝 x) (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,hf₀,Complex.zero_im] using Complex.continuous_im.continuousAt.tendsto.comp hf
  have hstrip := him.eventually (Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos)
  filter_upwards [he,hstrip] with y hy hh
  rw [←hy,Complex.log_exp hh.1 hh.2.le]

end JointDickman

end OAI
