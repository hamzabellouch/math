import OAI.Analysis.IrrationalRotation.Analysis.ParameterAttenuationConsequences
import OAI.Analysis.IrrationalRotation.Analysis.ConvolutionUniformConstant

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
open InvariantProjection.ConditionalConvolution

namespace Invariant233.ProductScaleLaws
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem conditional_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (n : ℕ) {c η δ : ℝ}
    (d : Data Ω μ (p.K n) (p.coefficientBound n)
      (1 / ((n + 1 : ℕ) : ℝ)) c η δ)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) :
    c * p.ε n ≤ ((2 * p.K n + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) := by
  apply d.obstruction_of_coefficient_bound (hp.epsilon_pos n).le _ hη hδ
  exact hp.polynomial_lower n

theorem no_conditional_data_at_stage {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (n : ℕ) (c : ℝ) (hc : 1 / ((n + 1 : ℕ) : ℝ) < c) :
    ¬ Nonempty (Data Ω μ (p.K n) (p.coefficientBound n)
      (1 / ((n + 1 : ℕ) : ℝ)) c
      (Real.exp (-p.L n)) (Real.exp (-p.L n / 400))) := by
  rintro ⟨d⟩
  have h := hp.conditional_bound n d (Real.exp_pos _).le (Real.exp_pos _).le
  have h' : c * p.ε n ≤ (2 * (p.K n : ℝ) + 1) *
      (Real.exp (-p.L n) + 2 * Real.sqrt (Real.exp (-p.L n / 400))) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h
  exact ConvolutionContradiction.fixed_stage_contradiction c (p.ε n)
    ((n + 1 : ℕ) : ℝ) (hp.epsilon_pos n) hc (h'.trans (hp.conditional_tail_le n))

theorem not_eventually_conditional_data
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ n in atTop,
      Nonempty (Data (Ω n) (μ n) (p.K n) (p.coefficientBound n)
        (1 / ((n + 1 : ℕ) : ℝ)) c
        (Real.exp (-p.L n)) (Real.exp (-p.L n / 400))) := by
  intro h
  apply hp.not_eventually_conditional_obstruction c hc
  filter_upwards [h] with n hn
  obtain ⟨d⟩ := hn
  have hb := hp.conditional_bound n d (Real.exp_pos _).le (Real.exp_pos _).le
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb

end Invariant233.ProductScaleLaws

end

end OAI
