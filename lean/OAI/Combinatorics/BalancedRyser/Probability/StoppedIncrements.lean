import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} {X : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}

theorem stopped_increment_eq_indicator (j : ℕ) :
    (fun ω ↦ stoppedProcess X τ (j + 1) ω - stoppedProcess X τ j ω) =
      {ω | (j : WithTop ℕ) < τ ω}.indicator (fun ω ↦ X (j + 1) ω - X j ω) := by
  classical
  funext ω
  by_cases hactive : (j : WithTop ℕ) < τ ω
  · have hj1 : ((j + 1 : ℕ) : WithTop ℕ) ≤ τ ω := by
      cases heq : τ ω with
      | top => simp
      | coe k =>
        rw [heq] at hactive
        have hjk : j < k := WithTop.coe_lt_coe.mp hactive
        exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt hjk)
    rw [stoppedProcess_eq_of_le (u := X) (i := j + 1) hj1,
      stoppedProcess_eq_of_le (u := X) (i := j) hactive.le]
    simp [Set.indicator, hactive]
  · have hτj : τ ω ≤ (j : WithTop ℕ) := le_of_not_gt hactive
    have hτj1 : τ ω ≤ ((j + 1 : ℕ) : WithTop ℕ) :=
      hτj.trans (by exact_mod_cast Nat.le_succ j)
    rw [stoppedProcess_eq_of_ge (u := X) (i := j + 1) hτj1,
      stoppedProcess_eq_of_ge (u := X) (i := j) hτj]
    simp [Set.indicator, hactive]

theorem stopped_increment_abs_le {j : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hX : ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L) :
    ∀ᵐ ω ∂μ, |stoppedProcess X τ (j + 1) ω - stoppedProcess X τ j ω| ≤ L := by
  classical
  filter_upwards [hX] with ω hω
  rw [congrFun (stopped_increment_eq_indicator (X := X) (τ := τ) j) ω]
  by_cases hactive : (j : WithTop ℕ) < τ ω
  · simpa [Set.indicator, hactive] using hω
  · simpa [Set.indicator, hactive] using hL

theorem condExp_stopped_increment
    {ℱ : Filtration ℕ mΩ} (hτ : IsStoppingTime ℱ τ) (j : ℕ)
    (hi : Integrable (fun ω ↦ X (j + 1) ω - X j ω) μ) :
    μ[fun ω ↦ stoppedProcess X τ (j + 1) ω - stoppedProcess X τ j ω | ℱ j] =ᵐ[μ]
      {ω | (j : WithTop ℕ) < τ ω}.indicator
        (μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j]) := by
  have hs : MeasurableSet[ℱ j] {ω | (j : WithTop ℕ) < τ ω} := by
    convert (hτ j).compl using 1
    ext ω
    simp
  rw [stopped_increment_eq_indicator]
  exact condExp_indicator hi hs

theorem condExp_stopped_increment_nonneg
    {ℱ : Filtration ℕ mΩ} (hτ : IsStoppingTime ℱ τ) (j : ℕ)
    (hi : Integrable (fun ω ↦ X (j + 1) ω - X j ω) μ)
    (hd : ∀ᵐ ω ∂μ, 0 ≤ μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) :
    ∀ᵐ ω ∂μ,
      0 ≤ μ[fun ω ↦ stoppedProcess X τ (j + 1) ω - stoppedProcess X τ j ω | ℱ j] ω := by
  classical
  filter_upwards [condExp_stopped_increment hτ j hi, hd] with ω heq hdω
  rw [heq]
  by_cases hactive : (j : WithTop ℕ) < τ ω
  · simpa [Set.indicator, hactive] using hdω
  · simp [Set.indicator, hactive]

theorem condExp_stopped_increment_le
    {ℱ : Filtration ℕ mΩ} (hτ : IsStoppingTime ℱ τ) (j : ℕ)
    (hi : Integrable (fun ω ↦ X (j + 1) ω - X j ω) μ)
    {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ᵐ ω ∂μ, μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω ≤ D) :
    ∀ᵐ ω ∂μ,
      μ[fun ω ↦ stoppedProcess X τ (j + 1) ω - stoppedProcess X τ j ω | ℱ j] ω ≤ D := by
  classical
  filter_upwards [condExp_stopped_increment hτ j hi, hd] with ω heq hdω
  rw [heq]
  by_cases hactive : (j : WithTop ℕ) < τ ω
  · simpa [Set.indicator, hactive] using hdω
  · simpa [Set.indicator, hactive] using hD

end Balanced

end OAI
