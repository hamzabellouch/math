import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowLaguerreParameterBound
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! # Parameter holomorphy of the actual Laguerre coefficients -/

open MeasureTheory Filter Topology Set

namespace DefocusingNLS

theorem differentiableAt_laguerreIntegrand_parameter (q : ℂ) (m n : ℕ) (s : ℂ) (t : ℝ)
    (hq : -1 < q.re) (hsre : s.re = 0) (ht : 0 < t) :
    DifferentiableAt ℂ (fun z => laguerreIntegrand (shiftedSlowDerivative 0 z m s) n t) q := by
  have hx : 0 < ((t : ℂ) - s).re := by simpa [hsre] using ht
  have h := differentiableAt_regularizedSlowSolution_parameter_closed q m ((t : ℂ) - s) hq hx.le
    (by intro hz; simp [hz] at hx)
  exact (h.const_mul (Real.exp (-t) : ℂ)).mul_const (laguerreValue n t)

noncomputable def slowLaguerreParameterDerivative (q : ℂ) (m n : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  deriv (fun z => laguerreIntegrand (shiftedSlowDerivative 0 z m s) n t) q

theorem aestronglyMeasurable_slowLaguerreParameterDerivative (q : ℂ) (m n : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    AEStronglyMeasurable (slowLaguerreParameterDerivative q m n s) (volume.restrict (Ioi 0)) := by
  let ε : ℕ → ℂ := fun j => ((1 / ((j : ℝ) + 1) : ℝ) : ℂ)
  have hε : Tendsto ε atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall ?_⟩
    · simpa only [ε, Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · intro j
      change ε j ≠ 0
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hmeas (j : ℕ) : AEStronglyMeasurable
      (fun t => (ε j)⁻¹ • (laguerreIntegrand (shiftedSlowDerivative 0 (q + ε j) m s) n t -
        laguerreIntegrand (shiftedSlowDerivative 0 q m s) n t)) (volume.restrict (Ioi 0)) := by
    have hqj : -1 < (q + ε j).re := by
      change -1 < q.re + 1 / ((j : ℝ) + 1)
      have hp : 0 < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    convert! ((integrableOn_laguerreIntegrand_shiftedSlowDerivative 0 n (q + ε j) m s hqj hsre hsim).aestronglyMeasurable.sub
      (integrableOn_laguerreIntegrand_shiftedSlowDerivative 0 n q m s hq hsre hsim).aestronglyMeasurable).const_smul ((ε j)⁻¹) using 1
  apply aestronglyMeasurable_of_tendsto_ae atTop hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (differentiableAt_laguerreIntegrand_parameter q m n s t hq hsre ht).hasDerivAt.tendsto_slope_zero.comp hε

theorem differentiableAt_slowLaguerreCoefficient (q : ℂ) (m n : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    DifferentiableAt ℂ (fun z => slowLaguerreCoefficient z m s n) q := by
  obtain ⟨ρ, hρ, bound, hbound, hb⟩ := exists_slowLaguerre_parameter_majorant q m n s hq hsre hsim
  have hinc (z : ℂ) (hz : z ∈ Metric.ball q ρ) :
      Metric.closedBall z ρ ⊆ Metric.closedBall q (2 * ρ) := by
    intro w hw
    have ht := dist_triangle w z q
    have h₁ := Metric.mem_closedBall.mp hw
    have h₂ := Metric.mem_ball.mp hz
    apply Metric.mem_closedBall.mpr
    linarith
  have hd (t : ℝ) (ht : 0 < t) (z : ℂ) (hz : z ∈ Metric.ball q ρ) :
      ‖slowLaguerreParameterDerivative z m n s t‖ ≤ bound t / ρ := by
    have hf : DifferentiableOn ℂ
        (fun w => laguerreIntegrand (shiftedSlowDerivative 0 w m s) n t)
        (Metric.closedBall q (2 * ρ)) := by
      intro w hw
      exact (differentiableAt_laguerreIntegrand_parameter w m n s t (hb w hw).1 hsre ht).differentiableWithinAt
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
      (hf.diffContOnCl_ball (hinc z hz))
    intro w hw
    exact (hb w (hinc z hz (Metric.sphere_subset_closedBall hw))).2 t ht
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun z t => laguerreIntegrand (shiftedSlowDerivative 0 z m s) n t)
    (F' := fun z t => slowLaguerreParameterDerivative z m n s t)
    (bound := fun t => bound t / ρ) (Metric.ball_mem_nhds q hρ)
    (by
      filter_upwards [Metric.ball_mem_nhds q hρ] with z hz
      exact (integrableOn_laguerreIntegrand_shiftedSlowDerivative 0 n z m s
        (hb z (Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hz))).1 hsre hsim).aestronglyMeasurable)
    (integrableOn_laguerreIntegrand_shiftedSlowDerivative 0 n q m s hq hsre hsim)
    (aestronglyMeasurable_slowLaguerreParameterDerivative q m n s hq hsre hsim)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro z hz
      exact hd t ht z hz)
    (hbound.div_const ρ)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro z hz
      exact (differentiableAt_laguerreIntegrand_parameter z m n s t
        (hb z (Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hz))).1 hsre ht).hasDerivAt)).2.differentiableAt

end DefocusingNLS

end OAI
