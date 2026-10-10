import OAI.Computability.UniqueGames.Decoding.ActualSeedSamplingLemmas
import OAI.Computability.UniqueGames.Decoding.SelectedFiberLaw
import OAI.Computability.UniqueGames.Decoding.SparseLawLemmas

namespace OAI

section

/-! The full selected-witness argument on the actual projected experiment.
The variation comparison precedes all conditioning. Its visible event then
pays the independent private decoder success on every selected datum. -/

namespace UniqueGamesTheorem.Decoder.ActualProjectedTransfer

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

variable {k s d r : ℕ}

def slopeVariation (k s d : ℕ) (β : ℝ) : ℝ :=
  Foundations.Information.totalVariation
    (SparseLaw.independentWeights
      (SparseLaw.mixture β (SparseLaw.singletonPairWeights (Ambient s d))) k)
    (SparseLaw.uniformWeights (Fin k → Ambient s d × Ambient s d))

/-- The actual complete-data event has positive mass depending only on the
fixed inverse and alphabet parameters. -/
theorem visible_mass (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
    ConstantSelection.visibleMass α g₀ s r ≤
      ((ActualSeedEvents.law S k s d r β hβ hβ').pushforward AdviceLaw.completeObserve).probability
        (VisibleTransfer.visibleWitness (ActualSeedEvents.law S k s d r β hβ hβ')
          AdviceLaw.completeObserve (ActualSeedEvents.slice S k s d r labeling α)
          (ActualSeedEvents.targetHit S k s d r labeling α) (α / 4)) := by
  have htv := (ActualSeedVariation.actual_totalVariation_le_slope S k s d r β hβ hβ').trans hvariation
  have h := VisibleTransfer.projected_witness_mass
    (ActualEvents.unrestricted S k s d r) (ActualSeedEvents.law S k s d r β hβ hβ')
    (ActualSeedEvents.pad S k s d r) AdviceLaw.completeObserve
    (ActualEvents.sliceEvent S k s d r labeling α) (ActualEvents.targetHit S k s d r labeling α)
    α g₀ (1 / (2 : ℝ) ^ (s * r)) hα.le
    (ActualEvents.slice_probability_lower S k s d r labeling α g₀ hgood)
    (ActualEvents.target_probability_lower S k s d r labeling α)
    (ConstantSelection.variationBudget_suffices hα s r htv)
  have hc : α * g₀ * (1 / (2 : ℝ) ^ (s * r)) / 8 =
      ConstantSelection.visibleMass α g₀ s r := by
    unfold ConstantSelection.visibleMass
    ring
  rw [hc] at h
  exact h

/-- Integrating a pointwise lower bound over a genuine probability event. -/
theorem event_expectation_lower {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (event : Ω → Bool) (f : Ω → ℝ)
    (γ₁ γ₂ : ℝ) (hγ₂ : 0 ≤ γ₂) (hf : ∀ x, 0 ≤ f x)
    (hmass : γ₁ ≤ μ.probability event)
    (hpoint : ∀ x, event x = true → γ₂ ≤ f x) :
    γ₁ * γ₂ ≤ μ.expectation f := by
  have hweighted : μ.probability event * γ₂ ≤ μ.expectation f := by
    unfold FiniteDistribution.probability FiniteDistribution.expectation
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : event x = true
    · simp only [hx, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left (hpoint x hx) (μ.nonnegative x)
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, zero_mul]
      exact mul_nonneg (μ.nonnegative x) (hf x)
  exact (mul_le_mul_of_nonneg_right hmass hγ₂).trans hweighted

/-- End-to-end lower bound for actual local stochastic responses. No hidden
matrix, selected witness, or opposing observation is passed to a prover. -/
theorem actual_success_lower (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
    ConstantSelection.decodingMass α g₀ s r ≤
      (ActualSeedEvents.law S k s d r β hβ hβ').expectation
        (fun seed => VisiblePolicies.observedAgreement S labeling
          (SelectedPolicies.goodPredicate S labeling α hα hsmall)
          (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) := by
  let μ := ActualSeedEvents.law S k s d r β hβ hβ'
  let good := SelectedPolicies.goodPredicate S labeling α hα hsmall
  have h := event_expectation_lower (μ.pushforward AdviceLaw.completeObserve)
    (VisibleTransfer.visibleWitness μ AdviceLaw.completeObserve
      (ActualSeedEvents.slice S k s d r labeling α)
      (ActualSeedEvents.targetHit S k s d r labeling α) (α / 4))
    (ActualConditionalLaw.datumAgreement S labeling good)
    (ConstantSelection.visibleMass α g₀ s r) (ConstantSelection.conditionalMass α s r)
    (ConstantSelection.conditionalMass_pos hα s r).le
    (ActualConditionalLaw.datumAgreement_nonneg S labeling good)
    (visible_mass S labeling α g₀ β hα hβ hβ' hgood hvariation)
    (SelectedFiberLaw.visibleWitness_decoding S labeling α hα hsmall β hβ hβ')
  rw [FiniteDistribution.expectation_pushforward] at h
  unfold ConstantSelection.decodingMass
  convert h using 1
  apply FiniteDistribution.expectation_congr
  intro seed
  exact ActualConditionalLaw.observedAgreement_seed S labeling good seed

end
end UniqueGamesTheorem.Decoder.ActualProjectedTransfer

end

end OAI
