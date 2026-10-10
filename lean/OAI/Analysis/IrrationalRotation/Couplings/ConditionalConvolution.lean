import OAI.Analysis.IrrationalRotation.Model.ConditionalConvolution
import OAI.Analysis.IrrationalRotation.Couplings.ConditionalL2Tail
import OAI.Analysis.IrrationalRotation.Analysis.OmittedEvents
import OAI.Analysis.IrrationalRotation.Analysis.FiniteWindowIntegralLower
import OAI.Analysis.IrrationalRotation.Couplings.ConditionalConvolutionPointwise

namespace OAI

open MeasureTheory
open scoped ENNReal lp ComplexConjugate

noncomputable section

namespace InvariantProjection.ConditionalConvolution

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable {K : ℕ} {D a c η δ : ℝ}

def exceptionalTail (H : ℤ → Set Ω) (K n : ℕ)
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (ω : Ω) : ℝ :=
  ∑' v : ℤ, (omittedEvent H K n v).indicator
    (fun ω => ‖ξ ω v‖ * ‖γ ω ((n : ℤ) + v)‖) ω

omit mΩ in
theorem exceptionalTail_nonneg (H : ℤ → Set Ω) (K n : ℕ)
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (ω : Ω) :
    0 ≤ exceptionalTail H K n ξ γ ω := by
  apply tsum_nonneg
  intro v
  exact Set.indicator_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ω

omit mΩ in
theorem exceptionalTail_eq_productMask (H : ℤ → Set Ω) (K n : ℕ)
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) :
    exceptionalTail H K n ξ γ = fun ω => ∑' v : ℤ,
      ({z : Ω × ℤ | z.1 ∈ omittedEvent H K n z.2}).indicator
        (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 ((n : ℤ) + z.2)‖) (ω, v) := by
  funext ω
  unfold exceptionalTail
  apply tsum_congr
  intro v
  by_cases hv : ω ∈ omittedEvent H K n v <;> simp [hv]

omit mΩ in
theorem exceptionalTail_eq_indicatorOne (H : ℤ → Set Ω) (K n : ℕ)
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (ω : Ω) :
    exceptionalTail H K n ξ γ ω = ∑' v : ℤ,
      (omittedEvent H K n v).indicator (fun _ => (1 : ℝ)) ω *
        (‖ξ ω v‖ * ‖γ ω ((n : ℤ) + v)‖) := by
  unfold exceptionalTail
  apply tsum_congr
  intro v
  by_cases hv : ω ∈ omittedEvent H K n v <;> simp [hv]

namespace Data

variable (d : Data Ω μ K D a c η δ)

theorem coeffA_measurable (v : ℤ) : Measurable (fun ω => coeffA d.ξ d.Fx ω v) := by
  have hx : StronglyMeasurable (fun ω => d.ξ ω v) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 v).continuous.comp_stronglyMeasurable
      (d.ξ_measurable.mono d.mX_le)
  exact hx.measurable.div (Complex.continuous_ofReal.measurable.comp (d.Fx_measurable v))

theorem coeffB_measurable (v : ℤ) : Measurable (fun ω => coeffB d.γ d.Fy ω v) := by
  have hy : StronglyMeasurable (fun ω => d.γ ω (-v)) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-v)).continuous.comp_stronglyMeasurable
      (d.γ_measurable.mono d.mY_le)
  exact (Complex.continuous_ofReal.measurable.comp (d.Fy_measurable (-v))).mul
    (Complex.continuous_conj.measurable.comp hy.measurable)

theorem integrableOn_norm_truncated [IsFiniteMeasure μ] (n : ℕ) :
    IntegrableOn (fun ω => ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖) d.E μ := by
  exact Invariant233.FiniteWindow.integrableOn_norm_convolution μ d.E
    (measure_lt_top μ d.E) K n D (coeffA d.ξ d.Fx) (coeffB d.γ d.Fy)
    d.coeffA_measurable d.coeffB_measurable
    (d.coefficient_bounds.mono fun _ h => h.1)
    (d.coefficient_bounds.mono fun _ h => h.2.1)

theorem first_tail_bound [IsProbabilityMeasure μ] (n : ℕ) (hδ : 0 ≤ δ) :
    Integrable (exceptionalTail d.H₁ K n d.ξ d.γ) μ ∧
    (∫ ω, exceptionalTail d.H₁ K n d.ξ d.γ ω ∂μ) ≤ Real.sqrt δ := by
  have h := integral_l2_masked_tail_le_of_condExp (mΩ := mΩ)
    d.ξ d.γ (d.γ_measurable.mono d.mY_le) d.ξ_unit d.γ_unit
    (Equiv.addLeft (n : ℤ))
    (measurableSet_omittedMask d.H₁ K n (fun k _ => d.H₁_measurable k))
    d.mX_le d.ξ_measurable hδ
    (condExp_omittedMask_section_le μ d.mX d.H₁ K n hδ d.conditional₁)
  rw [exceptionalTail_eq_productMask]
  exact h.2

theorem second_tail_bound [IsProbabilityMeasure μ] (n : ℕ) (hδ : 0 ≤ δ) :
    Integrable (exceptionalTail d.H₂ K n d.ξ d.γ) μ ∧
    (∫ ω, exceptionalTail d.H₂ K n d.ξ d.γ ω ∂μ) ≤ Real.sqrt δ := by
  have h := integral_l2_masked_tail_le_of_condExp_right (mΩ := mΩ)
    d.ξ d.γ (d.ξ_measurable.mono d.mX_le) d.ξ_unit d.γ_unit
    (Equiv.addLeft (n : ℤ))
    (measurableSet_omittedMask d.H₂ K n (fun k _ => d.H₂_measurable k))
    d.mY_le d.γ_measurable hδ
    (condExp_omittedMask_section_le μ d.mY d.H₂ K n hδ d.conditional₂)
  rw [exceptionalTail_eq_productMask]
  exact h

theorem integral_truncated_le_of_pointwise [IsProbabilityMeasure μ]
    (n : ℕ) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hpoint : ∀ᵐ ω ∂μ.restrict d.E,
      ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖ ≤
        η + exceptionalTail d.H₁ K n d.ξ d.γ ω + exceptionalTail d.H₂ K n d.ξ d.γ ω) :
    (∫ ω in d.E, ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖ ∂μ) ≤
      η + 2 * Real.sqrt δ := by
  obtain ⟨ht₁, hb₁⟩ := d.first_tail_bound n hδ
  obtain ⟨ht₂, hb₂⟩ := d.second_tail_bound n hδ
  have hi : Integrable (d.E.indicator (fun ω =>
      ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖)) μ :=
    (integrable_indicator_iff d.E_measurable).mpr (d.integrableOn_norm_truncated n)
  have hfull : ∀ᵐ ω ∂μ,
      d.E.indicator (fun ω => ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖) ω ≤
      η + exceptionalTail d.H₁ K n d.ξ d.γ ω + exceptionalTail d.H₂ K n d.ξ d.γ ω := by
    filter_upwards [(ae_restrict_iff' d.E_measurable).mp hpoint] with ω hω
    by_cases hE : ω ∈ d.E
    · simpa only [Set.indicator_of_mem hE] using hω hE
    · rw [Set.indicator_of_notMem hE]
      exact add_nonneg (add_nonneg hη (exceptionalTail_nonneg _ _ _ _ _ _))
        (exceptionalTail_nonneg _ _ _ _ _ _)
  have hiR := ((integrable_const η).add ht₁).add ht₂
  have hbound := integral_mono_ae hi hiR hfull
  rw [integral_indicator d.E_measurable] at hbound
  have heval : (∫ ω, ((fun _ : Ω => η) + exceptionalTail d.H₁ K n d.ξ d.γ +
      exceptionalTail d.H₂ K n d.ξ d.γ) ω ∂μ) =
      η + (∫ ω, exceptionalTail d.H₁ K n d.ξ d.γ ω ∂μ) +
      (∫ ω, exceptionalTail d.H₂ K n d.ξ d.γ ω ∂μ) := by
    calc
      _ = (∫ ω, ((fun _ : Ω => η) + exceptionalTail d.H₁ K n d.ξ d.γ) ω ∂μ) +
          ∫ ω, exceptionalTail d.H₂ K n d.ξ d.γ ω ∂μ :=
        integral_add ((integrable_const η).add ht₁) ht₂
      _ = ((∫ _ : Ω, η ∂μ) + ∫ ω, exceptionalTail d.H₁ K n d.ξ d.γ ω ∂μ) +
          ∫ ω, exceptionalTail d.H₂ K n d.ξ d.γ ω ∂μ := by
        rw [show (∫ ω, ((fun _ : Ω => η) + exceptionalTail d.H₁ K n d.ξ d.γ) ω ∂μ) =
          (∫ _ : Ω, η ∂μ) + ∫ ω, exceptionalTail d.H₁ K n d.ξ d.γ ω ∂μ from
          integral_add (integrable_const η) ht₁]
      _ = _ := by simp
  rw [heval] at hbound
  linarith

theorem pointwise_truncated_bound (n : ℕ) (hn : n ≤ 2 * K) (hη : 0 ≤ η) :
    ∀ᵐ ω ∂μ.restrict d.E,
      ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖ ≤
        η + exceptionalTail d.H₁ K n d.ξ d.γ ω + exceptionalTail d.H₂ K n d.ξ d.γ ω := by
  filter_upwards [ae_restrict_of_ae d.ξ_unit, ae_restrict_of_ae d.γ_unit,
    ae_restrict_of_ae (d.ratio_bounds n hn), ae_restrict_of_ae (d.zero_convolution n hn),
    d.attenuation] with ω hξ hγ hr hz ht
  have hz' : (∑' v : ℤ, (d.ξ ω v / (d.Fx ω v : ℂ)) *
      ((d.Fy ω ((n : ℤ) + v) : ℂ) * conj (d.γ ω ((n : ℤ) + v)))) = 0 := by
    simpa only [coeffA, coeffB, neg_sub, neg_neg, sub_neg_eq_add, add_comm] using hz
  have h := pointwise_bound K n (d.Fx ω) (d.Fy ω) (d.ξ ω) (d.γ ω)
    hξ hγ η hη d.H₁ d.H₂ ω hr hz' ht
  rw [← exceptionalTail_eq_indicatorOne, ← exceptionalTail_eq_indicatorOne] at h
  exact h

theorem obstruction_of_pointwise [IsProbabilityMeasure μ]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcoeff : ∀ A B : ℤ → ℂ,
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖A v‖ ≤ D) →
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖B v‖ ≤ D) →
      a ≤ ‖A 0‖ → a ≤ ‖B 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖truncated K n A B‖)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hpoint : ∀ n : ℕ, n ≤ 2 * K → ∀ᵐ ω ∂μ.restrict d.E,
      ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖ ≤
        η + exceptionalTail d.H₁ K n d.ξ d.γ ω + exceptionalTail d.H₂ K n d.ξ d.γ ω) :
    c * ε ≤ ((2 * K + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) := by
  apply Invariant233.FiniteWindow.finite_sum_obstruction μ d.E (2 * K + 1)
    (fun n ω => ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖)
    c ε (η + 2 * Real.sqrt δ) hε d.E_mass
  · intro n _
    exact d.integrableOn_norm_truncated n
  · exact Invariant233.FiniteWindow.integral_lower_of_sum_bound μ K D a ε hcoeff
      d.E (coeffA d.ξ d.Fx) (coeffB d.γ d.Fy)
      d.coeffA_measurable d.coeffB_measurable d.coefficient_bounds
  · intro n hn
    exact d.integral_truncated_le_of_pointwise n hη hδ
      (hpoint n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))

end Data

theorem conditional_convolution_obstruction
    (K : ℕ) (D a : ℝ) (ha : 0 < a) :
    ∃ ε > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (c η δ : ℝ),
      0 ≤ η → 0 ≤ δ → ∀ _ : Data Ω μ K D a c η δ,
      c * ε ≤ ((2 * K + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) := by
  obtain ⟨ε, hε, hcoeff⟩ := Invariant233.FiniteWindow.uniform_convolution_sum_lower_bound K D a ha
  refine ⟨ε, hε, ?_⟩
  intro Ω mΩ μ hμ c η δ hη hδ d
  exact d.obstruction_of_pointwise hε.le hcoeff hη hδ
    (fun n hn => d.pointwise_truncated_bound n hn hη)

end InvariantProjection.ConditionalConvolution

end

end OAI
