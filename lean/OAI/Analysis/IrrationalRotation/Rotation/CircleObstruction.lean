import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Analysis.ConvolutionUniformConstant
import OAI.Analysis.IrrationalRotation.Analysis.ConvolutionContradiction

namespace OAI

noncomputable section

open MeasureTheory Filter
open InvariantProjection.ConditionalConvolution

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

include hp

theorem convolution_sum_lower (j : ℕ) (hj : 1 ≤ j) :
    ∀ A B : ℤ → ℂ,
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) → ‖A v‖ ≤ p.coefficientBound j) →
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) → ‖B v‖ ≤ p.coefficientBound j) →
      1 / (j : ℝ) ≤ ‖A 0‖ → 1 / (j : ℝ) ≤ ‖B 0‖ →
      p.ε j ≤ ∑ n ∈ Finset.range (2 * p.K j + 1),
        ‖truncated (p.K j) n A B‖ := by
  apply FiniteWindow.convolution_sum_lower_bound_of_supported_bound
    (p.K j) (p.coefficientBound j) (1 / (j : ℝ)) (p.ε j)
  simpa only [CircleParameterData.convolutionCoefficient] using hp.polynomial_lower j hj

theorem conditional_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (j : ℕ) (hj : 1 ≤ j) {c η δ : ℝ}
    (d : Data Ω μ (p.K j) (p.coefficientBound j) (1 / (j : ℝ)) c η δ)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) :
    c * p.ε j ≤ ((2 * p.K j + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) := by
  exact d.obstruction_of_pointwise (hp.epsilon_pos j hj).le
    (hp.convolution_sum_lower j hj) hη hδ
    (fun n hn => d.pointwise_truncated_bound n hn hη)

theorem no_conditional_data_at_stage {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (j : ℕ) (hj : 1 ≤ j) (c : ℝ) (hc : 1 / (j : ℝ) < c) :
    ¬ Nonempty (Data Ω μ (p.K j) (p.coefficientBound j) (1 / (j : ℝ)) c
      (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  rintro ⟨d⟩
  have hbound := hp.conditional_bound j hj d
    (Real.exp_pos _).le (Real.exp_pos _).le
  have hchoice := hp.polynomial_attenuation j hj
  have htail := ConvolutionContradiction.coefficient_tail_le
    (p.K j) (p.L j) (p.ε j) (j : ℝ) (hp.L_pos j hj).le
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat] using hchoice)
  apply ConvolutionContradiction.fixed_stage_contradiction c (p.ε j) (j : ℝ)
    (hp.epsilon_pos j hj) hc
  apply le_trans ?_ htail
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] using hbound

theorem not_eventually_conditional_data
    {Ω : ℕ → Type*} [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ j in atTop,
      Nonempty (Data (Ω j) (μ j) (p.K j) (p.coefficientBound j)
        (1 / (j : ℝ)) c (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  intro hdata
  have hsmall : ∀ᶠ j : ℕ in atTop, 1 / (j : ℝ) < c :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hc)
  obtain ⟨j, hj, hsmallj, hd⟩ :=
    ((eventually_ge_atTop 1).and (hsmall.and hdata)).exists
  exact hp.no_conditional_data_at_stage j hj c hsmallj hd

end Invariant233.CircleParameterLaws

end

end OAI
