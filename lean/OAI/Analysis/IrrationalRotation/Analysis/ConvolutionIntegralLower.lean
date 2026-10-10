import OAI.Analysis.IrrationalRotation.Analysis.FiniteConvolution

namespace OAI

open MeasureTheory

namespace InvariantProjection.FiniteConvolution

theorem sum_lower_of_coefficient_lower {K : ℕ} {ε : ℝ}
    (a b : Coefficients K)
    (h : ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct a b n‖) :
    ε ≤ ∑ n : Fin (2 * K + 1), ‖lowProduct a b n‖ := by
  obtain ⟨n, hn⟩ := h
  exact hn.trans (Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ n))

theorem integral_lower_of_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℕ) (D δ ε : ℝ)
    (hcoeff : ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a (center K)‖ → δ ≤ ‖b (center K)‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖lowProduct a b n‖)
    (E : Set Ω) (a b : Ω → Coefficients K)
    (hint : IntegrableOn (fun ω => ∑ n : Fin (2 * K + 1),
      ‖lowProduct (a ω) (b ω) n‖) E μ)
    (hE : ∀ᵐ ω ∂μ.restrict E,
      (∀ i, ‖a ω i‖ ≤ D) ∧ (∀ i, ‖b ω i‖ ≤ D) ∧
      δ ≤ ‖a ω (center K)‖ ∧ δ ≤ ‖b ω (center K)‖) :
    ε * μ.real E ≤ ∫ ω in E, ∑ n : Fin (2 * K + 1),
      ‖lowProduct (a ω) (b ω) n‖ ∂μ := by
  have hpoint : ∀ᵐ ω ∂μ.restrict E,
      ε ≤ ∑ n : Fin (2 * K + 1), ‖lowProduct (a ω) (b ω) n‖ := by
    filter_upwards [hE] with ω hω
    exact sum_lower_of_coefficient_lower (a ω) (b ω)
      (hcoeff (a ω) (b ω) hω.1 hω.2.1 hω.2.2.1 hω.2.2.2)
  have h := integral_mono_ae (integrable_const ε) hint hpoint
  simpa only [setIntegral_const, smul_eq_mul, mul_comm] using h

theorem uniform_integral_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ (E : Set Ω) (a b : Ω → Coefficients K),
      IntegrableOn (fun ω => ∑ n : Fin (2 * K + 1),
        ‖lowProduct (a ω) (b ω) n‖) E μ →
      (∀ᵐ ω ∂μ.restrict E,
        (∀ i, ‖a ω i‖ ≤ D) ∧ (∀ i, ‖b ω i‖ ≤ D) ∧
        δ ≤ ‖a ω (center K)‖ ∧ δ ≤ ‖b ω (center K)‖) →
      ε * μ.real E ≤ ∫ ω in E, ∑ n : Fin (2 * K + 1),
        ‖lowProduct (a ω) (b ω) n‖ ∂μ := by
  obtain ⟨ε, hε, hcoeff⟩ := uniform_lower_bound K D δ hδ
  exact ⟨ε, hε, fun E a b hi hE =>
    integral_lower_of_uniform_bound μ K D δ ε hcoeff E a b hi hE⟩

end InvariantProjection.FiniteConvolution

end OAI
