import OAI.Combinatorics.BalancedRyser.Probability.BoundedDrift
import OAI.Combinatorics.BalancedRyser.Probability.IndependentDoobGrouping
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrialGrouping
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrialStep
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrials3

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials
open scoped _root_.Balanced

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ}

theorem martingale_abs_tail (hD : Martingale D ℱ μ)
    {T : ℕ} {L u : ℝ} (hT : 1 ≤ T) (hL : 0 < L) (hu : 0 < u)
    (hbound : ∀ j < T, ∀ᵐ ω ∂μ, |D (j + 1) ω - D j ω| ≤ L) :
    μ.real {ω | u ≤ |D T ω - D 0 ω|} ≤
      2 * Real.exp (-(u ^ 2) / (8 * (T : ℝ) * L ^ 2)) := by
  have htail := boundedDriftConcentration_proof μ ℱ D T L hT hL
    (fun j _ ↦ hD.stronglyMeasurable j) hbound u hu T le_rfl
  have hset : {ω | u ≤ |D T ω - D 0 ω|} =ᵐ[μ]
      {ω | u ≤ |D T ω - D 0 ω - ∑ j ∈ Finset.range T,
        μ[fun x ↦ D (j + 1) x - D j x | ℱ j] ω|} := by
    filter_upwards [ae_all_iff.2 (fun j ↦ martingale_increment_condExp_zero hD j)] with ω hω
    have hsum : (∑ j ∈ Finset.range T,
        μ[fun x ↦ D (j + 1) x - D j x | ℱ j] ω) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact hω j
    change (u ≤ |D T ω - D 0 ω|) =
      (u ≤ |D T ω - D 0 ω - ∑ j ∈ Finset.range T,
        μ[fun x ↦ D (j + 1) x - D j x | ℱ j] ω|)
    rw [hsum, sub_zero]
  rw [measureReal_congr hset]
  exact htail

theorem doob_abs_tail_of_increment_bound
    {T : ℕ} {A : Fin T → Type*} [∀ i, MeasurableSpace (A i)]
    (ξ : (i : Fin T) → Ω → A i) (hξ : ∀ i, Measurable (ξ i))
    {F : ((i : Fin T) → A i) → ℝ} (hF : Measurable F)
    (hY : Integrable (fun ω ↦ F (trialVector ξ ω)) μ)
    {c : Fin T → ℝ}
    (hbound : ∀ i : Fin T, ∀ᵐ ω ∂μ,
      |doobProcess ξ hξ (fun x ↦ F (trialVector ξ x)) μ (i.val + 1) ω -
        doobProcess ξ hξ (fun x ↦ F (trialVector ξ x)) μ i.val ω| ≤ c i)
    {L u : ℝ} (hT : 1 ≤ T) (hL : 0 < L) (hcL : ∀ i, c i ≤ L) (hu : 0 < u) :
    μ.real {ω | u ≤ |F (trialVector ξ ω) - ∫ x, F (trialVector ξ x) ∂μ|} ≤
      2 * Real.exp (-(u ^ 2) / (8 * (T : ℝ) * L ^ 2)) := by
  let Y : Ω → ℝ := fun ω ↦ F (trialVector ξ ω)
  have hD : Martingale (doobProcess ξ hξ Y μ) (prefixFiltration ξ hξ) μ :=
    martingale_condExp Y (prefixFiltration ξ hξ) μ
  have hb : ∀ j < T, ∀ᵐ ω ∂μ,
      |doobProcess ξ hξ Y μ (j + 1) ω - doobProcess ξ hξ Y μ j ω| ≤ L := by
    intro j hj
    filter_upwards [hbound ⟨j, hj⟩] with ω hω
    exact hω.trans (hcL ⟨j, hj⟩)
  have ht := martingale_abs_tail hD hT hL hu hb
  simpa only [Y, doobProcess_full ξ hξ hF hY, doobProcess_zero] using ht

end Balanced.IndependentTrials

namespace Balanced
open scoped _root_.Balanced

open IndependentTrials

universe u v

theorem independentTrialJumps_proof : IndependentTrialJumps.{u, v} := by
  intro T Ω mΩ μ hμ A mA ξ hξ F hF hind hY c hc hosc
  let Y : Ω → ℝ := fun ω ↦ F (trialVector ξ ω)
  let D := doobProcess ξ hξ Y μ
  have hD : Martingale D (prefixFiltration ξ hξ) μ :=
    martingale_condExp Y (prefixFiltration ξ hξ) μ
  have hbound (i : Fin T) :
      ∀ᵐ ω ∂μ, |D (i.val + 1) ω - D i.val ω| ≤ c i := by
    exact doob_increment_bound_of_grouping hξ F hF hY c hosc i
      (past_independent_current hξ hind i)
      (pastCurrent_independent_future hξ hind i)
      (comap_past_eq_prefixFiltration hξ i)
      (comap_past_current_eq_prefixFiltration hξ i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Filter.EventuallyEq.of_eq (doobProcess_zero ξ hξ Y)
  · exact Filter.EventuallyEq.of_eq (doobProcess_full ξ hξ hF hY)
  · intro i
    exact ⟨hbound i, martingale_increment_condVar_le hD i.val (hc i) (hbound i)⟩
  · intro L u hT hL hcL hu
    exact doob_abs_tail_of_increment_bound ξ hξ hF hY hbound hT hL hcL hu

end Balanced

end

end OAI
