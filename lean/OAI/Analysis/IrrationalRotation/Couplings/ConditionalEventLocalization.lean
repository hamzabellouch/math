import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Notation

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ProbabilityTheory

namespace Invariant233.ConditionalEventLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {m : MeasurableSpace Ω}

theorem condProb_mono_on (hm : m ≤ mΩ) {A B S : Set Ω}
    (hA : MeasurableSet[mΩ] A) (hB : MeasurableSet[mΩ] B) (hS : MeasurableSet[m] S)
    (hsub : ∀ᵐ ω ∂μ, ω ∈ S → ω ∈ A → ω ∈ B) :
    ∀ᵐ ω ∂μ, ω ∈ S → (μ⟦A | m⟧) ω ≤ (μ⟦B | m⟧) ω := by
  have hAi : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hA
  have hBi : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hB
  have hle : S.indicator (A.indicator (fun _ => (1 : ℝ))) ≤ᵐ[μ]
      S.indicator (B.indicator (fun _ => (1 : ℝ))) := by
    filter_upwards [hsub] with ω hω
    by_cases hs : ω ∈ S
    · simp only [indicator_of_mem hs]
      by_cases ha : ω ∈ A
      · simp only [indicator_of_mem ha, indicator_of_mem (hω hs ha), le_refl]
      · simp only [indicator_of_notMem ha]
        exact indicator_nonneg (fun _ _ => by norm_num) _
    · simp only [indicator_of_notMem hs, le_refl]
  have hc := condExp_mono (m := m) (hAi.indicator (hm _ hS))
    (hBi.indicator (hm _ hS)) hle
  filter_upwards [hc, condExp_indicator hAi hS, condExp_indicator hBi hS]
      with ω hle hleft hright
  intro hs
  rw [hleft, hright, indicator_of_mem hs, indicator_of_mem hs] at hle
  exact hle

theorem condProb_lower_on_of_forcing (hm : m ≤ mΩ) {A B S : Set Ω}
    (hA : MeasurableSet[mΩ] A) (hB : MeasurableSet[mΩ] B) (hS : MeasurableSet[m] S)
    (hsub : ∀ᵐ ω ∂μ, ω ∈ S → ω ∈ A → ω ∈ B)
    (r : Ω → ℝ) (hlower : ∀ᵐ ω ∂μ, ω ∈ S → r ω ≤ (μ⟦A | m⟧) ω) :
    ∀ᵐ ω ∂μ, ω ∈ S → r ω ≤ (μ⟦B | m⟧) ω := by
  filter_upwards [@condProb_mono_on Ω mΩ μ _ m hm A B S hA hB hS hsub, hlower] with ω hmono hlo
  exact fun hs => (hlo hs).trans (hmono hs)

end Invariant233.ConditionalEventLocalization

end

end OAI
