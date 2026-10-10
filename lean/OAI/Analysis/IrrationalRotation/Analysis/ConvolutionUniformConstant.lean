import OAI.Analysis.IrrationalRotation.Couplings.ConditionalConvolution

namespace OAI

open MeasureTheory

namespace InvariantProjection.ConditionalConvolution

theorem Data.obstruction_of_coefficient_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {K : ℕ} {D a c η δ ε : ℝ} (d : Data Ω μ K D a c η δ)
    (hε : 0 ≤ ε)
    (hcoeff : ∀ A B : ℤ → ℂ,
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖A v‖ ≤ D) →
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖B v‖ ≤ D) →
      a ≤ ‖A 0‖ → a ≤ ‖B 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖truncated K n A B‖)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) :
    c * ε ≤ ((2 * K + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) := by
  have hsum : ∀ A B : ℤ → ℂ,
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖A v‖ ≤ D) →
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖B v‖ ≤ D) →
      a ≤ ‖A 0‖ → a ≤ ‖B 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖truncated K n A B‖ := by
    intro A B hA hB hA0 hB0
    obtain ⟨n, hn, hnc⟩ := hcoeff A B hA hB hA0 hB0
    have hnmem : n ∈ Finset.range (2 * K + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
    exact hnc.trans (Finset.single_le_sum
      (fun k (_ : k ∈ Finset.range (2 * K + 1)) => norm_nonneg (truncated K k A B)) hnmem)
  exact d.obstruction_of_pointwise hε hsum hη hδ
    (fun n hn => d.pointwise_truncated_bound n hn hη)

theorem uniform_coefficient_and_conditional_bound
    (K : ℕ) (D a : ℝ) (ha : 0 < a) :
    ∃ ε > 0,
      (∀ A B : ℤ → ℂ,
        (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖A v‖ ≤ D) →
        (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖B v‖ ≤ D) →
        a ≤ ‖A 0‖ → a ≤ ‖B 0‖ →
        ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖truncated K n A B‖) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (c η δ : ℝ),
        0 ≤ η → 0 ≤ δ → ∀ _ : Data Ω μ K D a c η δ,
        c * ε ≤ ((2 * K + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ)) := by
  obtain ⟨ε, hε, hcoeff⟩ :=
    Invariant233.FiniteWindow.uniform_convolution_lower_bound K D a ha
  refine ⟨ε, hε, hcoeff, ?_⟩
  intro Ω mΩ μ hμ c η δ hη hδ d
  exact d.obstruction_of_coefficient_bound hε.le hcoeff hη hδ

end InvariantProjection.ConditionalConvolution

end OAI
