import OAI.NumberTheory.JointDickman.Analysis.LogRieszBounds
import Mathlib.Analysis.Asymptotics.Defs

namespace OAI

/-! # Uniformizing a logarithmic error on a multiplicative neighborhood -/
namespace JointDickman
open Filter Asymptotics
open scoped Topology

theorem isBigO_uniform_log_square {F : ℝ → ℝ} {β : ℝ}
    (h : F =O[atTop] (fun x => x^2*(Real.log x)^β)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ t ∈ Set.Icc (x/2) (2*x),
      |F t| ≤ C*x^2*(Real.log x)^β := by
  obtain ⟨C,hC,hbound⟩ := isBigO_iff'.mp h
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hbound
  refine ⟨C*(4*(2:ℝ)^(|β|)),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (2*x₀)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))] with x hx hlog t ht
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2*x₀ ≤ x := (le_max_right _ _).trans hx
  have ht₀ : x₀ ≤ t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hlogt : 0 < Real.log t := by
    have := (log_near_scale (by linarith : 0 < x) hlog ht).1
    linarith
  have hb := hx₀ t ht₀
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ t^2*(Real.log t)^β)] at hb
  calc
    _ ≤ C*(t^2*(Real.log t)^β) := hb
    _ ≤ C*((4*(2:ℝ)^(|β|))*x^2*(Real.log x)^β) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      have hg := logRieszMonomial_bound β (by linarith : 0 < x) hlog ht
      simpa only [logRieszMonomial,abs_of_nonneg (by positivity : 0 ≤ t^2*(Real.log t)^β)] using hg
    _ = _ := by ring

end JointDickman

end OAI
