import OAI.Probability.InvariantIsing.Haar.HaarPolynomialMoment

namespace OAI

/-! Passing polynomial Haar moments through uniform approximation. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem haar_uniform_polynomial_tendsto {N : ℕ} (p : ℕ → MatrixPolynomial N)
    (f : SpecialOrthogonal N → ℝ)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ U, |haarPolynomialValue (p n) U-f U| ≤ ε)
    (U : SpecialOrthogonal N) :
    Tendsto (fun n => haarPolynomialValue (p n) U) atTop (𝓝 (f U)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hu (ε/2) (half_pos hε)] with n hn
  rw [Real.dist_eq]
  exact (hn U).trans_lt (half_lt_self hε)

theorem haar_uniform_polynomial_integrals {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ]
    (p : ℕ → MatrixPolynomial N) (f : SpecialOrthogonal N → ℝ) (hf : Continuous f)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ U, |haarPolynomialValue (p n) U-f U| ≤ ε) :
    Tendsto (fun n => ∫ U, haarPolynomialValue (p n) U ∂μ) atTop (𝓝 (∫ U, f U ∂μ)) ∧
    ∀ t : ℝ, Tendsto (fun n => haarPolynomialMoment μ (p n) t) atTop
      (𝓝 (∫ U, Real.exp (t*f U) ∂μ)) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ᶠ n : ℕ in atTop, ∀ U, |haarPolynomialValue (p n) U| ≤ B+1 := by
    filter_upwards [hu 1 zero_lt_one] with n hn U
    have hbu : |f U| ≤ B := by simpa only [Real.norm_eq_abs] using hB U (mem_univ U)
    calc
      |haarPolynomialValue (p n) U| ≤ |haarPolynomialValue (p n) U-f U|+|f U| := by
        simpa only [sub_add_cancel] using abs_add_le (haarPolynomialValue (p n) U-f U) (f U)
      _ ≤ B+1 := by linarith [hn U]
  constructor
  · refine tendsto_integral_filter_of_dominated_convergence (fun _ => B+1)
      (Eventually.of_forall fun n => (continuous_haarPolynomialValue (p n)).measurable.aestronglyMeasurable)
      ?_ (integrable_const _) ?_
    · filter_upwards [hb] with n hn
      exact ae_of_all μ fun U => by simpa only [Real.norm_eq_abs] using hn U
    · exact ae_of_all μ fun U => haar_uniform_polynomial_tendsto p f hu U
  · intro t
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp (|t| *(B+1)))
      (Eventually.of_forall fun n => (Real.continuous_exp.comp (continuous_const.mul
        (continuous_haarPolynomialValue (p n)))).measurable.aestronglyMeasurable)
      ?_ (integrable_const _) ?_
    · filter_upwards [hb] with n hn
      apply ae_of_all
      intro U
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        t*haarPolynomialValue (p n) U ≤ |t*haarPolynomialValue (p n) U| := le_abs_self _
        _ = |t| * |haarPolynomialValue (p n) U| := abs_mul _ _
        _ ≤ |t| *(B+1) := mul_le_mul_of_nonneg_left (hn U) (abs_nonneg _)
    · exact ae_of_all μ fun U => Real.continuous_exp.continuousAt.tendsto.comp
        ((haar_uniform_polynomial_tendsto p f hu U).const_mul t)

end InvariantIsing

end

end OAI
