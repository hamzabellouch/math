import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

namespace OAI

/-! # Equality of entire functions from their real restrictions -/

namespace KadisonKastler

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem entire_eq_of_real {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (he : ∀ t : ℝ, f t = g t) : f = g := by
  apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).eq_of_frequently_eq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg) (z₀ := 0)
  apply mem_closure_ne_iff_frequently_within.mp
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((ε / 2 : ℝ) : ℂ), ⟨he _, ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff, Complex.ofReal_eq_zero]
    positivity
  · simpa only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < ε / 2)] using (half_lt_self hε)

end KadisonKastler

end OAI
