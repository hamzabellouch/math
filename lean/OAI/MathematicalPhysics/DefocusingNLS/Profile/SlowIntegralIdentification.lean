import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowSpatialDifferentiability
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowEulerDifferentialEquation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! # Identification of the two integrals on the initial half-planes -/

open MeasureTheory Filter Topology

namespace DefocusingNLS

theorem regularizedSlowSolution_eq_euler_complex (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    regularizedSlowSolution q m x = (Complex.Gamma q)⁻¹ * slowEulerIntegral q m x := by
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (regularizedSlowSolution q m) U :=
    (differentiableOn_regularizedSlowSolution q m (by linarith)).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun z => (Complex.Gamma q)⁻¹ * slowEulerIntegral q m z) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact ((hasDerivAt_slowEulerIntegral q m z hq hz).const_mul (Complex.Gamma q)⁻¹).differentiableAt.differentiableWithinAt
  have hconnected : IsPreconnected U := by
    exact ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm).isPreconnected
  have hclosure : (1 : ℂ) ∈ closure
      ({z | regularizedSlowSolution q m z = (Complex.Gamma q)⁻¹ * slowEulerIntegral q m z} \ {1}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let y : ℝ := 1 + ε / 2
    have hy : 0 < y := by dsimp [y]; linarith
    refine ⟨(y : ℂ), ⟨?_, ?_⟩, ?_⟩
    · exact regularizedSlowSolution_eq_euler q m hq hy
    · simp only [Set.mem_singleton_iff]
      intro h
      have : y = 1 := by exact_mod_cast h
      dsimp [y] at this
      linarith
    · have he : (1 : ℂ) - (y : ℂ) = ((-(ε / 2) : ℝ) : ℂ) := by
        dsimp [y]
        push_cast
        ring
      rw [dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_pos (half_pos hε)]
      exact half_lt_self hε
  exact hf.eqOn_of_preconnected_of_mem_closure hg hconnected
    (by change 0 < (1 : ℂ).re; norm_num) hclosure hx

end DefocusingNLS

end OAI
