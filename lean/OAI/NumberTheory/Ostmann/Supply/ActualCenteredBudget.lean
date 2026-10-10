import OAI.NumberTheory.Ostmann.Supply.ActualCenteredBudgetSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Finset Ostmann.Preliminaries
open scoped BigOperators

theorem eventually_actual_centered_energy_budgets (d : Decomposition) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
      ∀ T : Finset ℕ, (∀ t ∈ T, Squarefree t ∧ t ≤ R) →
        (∀ t ∈ T, ∑ p ∈ t.primeFactors, (1 : ℝ)/p ≤ 1/16) →
      (∑ t ∈ T, centeredEnergy (upperWindow d.A (R^2)) (actualSupport d) t ≤
        1536 * (R : ℝ) / ((upperWindow d.A (R^2)).card : ℝ) *
          Real.exp (C * Real.sqrt (Real.log (Real.log (R : ℝ))))) ∧
      (∑ t ∈ T, centeredEnergy (upperWindow d.B (R^2)) (actualSecondSupport d) t ≤
        1536 * (R : ℝ) / ((upperWindow d.B (R^2)).card : ℝ) *
          Real.exp (C * Real.sqrt (Real.log (Real.log (R : ℝ))))) := by
  obtain ⟨D, hD, hlog⟩ := eventually_actualLogBudget_le d
  refine ⟨16*D, by positivity, ?_⟩
  have hx : Tendsto (fun R : ℕ => (R : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hloglog := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hx)).eventually_gt_atTop 0
  filter_upwards [eventually_actualWindow_supports d, hlog, hloglog,
    eventually_ge_atTop 1] with R hs hbudget hll hR
  change 0 < Real.log (Real.log (R : ℝ)) at hll
  intro T hT hcop
  have hB : 0 < (16*D)*Real.sqrt (Real.log (Real.log (R : ℝ))) :=
    mul_pos (by positivity) (Real.sqrt_pos.mpr hll)
  have hmeanA : (∑ p ∈ CompletionCounting.primesUpTo R,
      |Real.log (supportRatio (actualSupport d) p)|/p) ≤
      ((16*D)*Real.sqrt (Real.log (Real.log (R : ℝ))))/16 := by
    rw [logBudget_actualSupport]
    calc
      _ ≤ D*Real.sqrt (Real.log (Real.log (R : ℝ))) := hbudget
      _ = _ := by ring
  have hmeanB : (∑ p ∈ CompletionCounting.primesUpTo R,
      |Real.log (supportRatio (actualSecondSupport d) p)|/p) ≤
      ((16*D)*Real.sqrt (Real.log (Real.log (R : ℝ))))/16 := by
    rw [logBudget_actualSecondSupport]
    calc
      _ ≤ D*Real.sqrt (Real.log (Real.log (R : ℝ))) := hbudget
      _ = _ := by ring
  constructor
  · exact centered_energy_sum_le (upperWindow d.A (R^2)) hs.1 (actualSupport d) R
      (by omega) (fun a ha => (mem_upperWindow.mp ha).2.1) hs.2.2.1
      (fun p hp _ => actualRatio_pos d hp) T hT hB hcop hmeanA
  · exact centered_energy_sum_le (upperWindow d.B (R^2)) hs.2.1 (actualSecondSupport d) R
      (by omega) (fun b hb => (mem_upperWindow.mp hb).2.1) hs.2.2.2
      (fun p hp _ => by rw [supportRatio_actualSecondSupport d hp]; exact inv_pos.mpr (actualRatio_pos d hp))
      T hT hB hcop hmeanB

theorem eventually_actualA_centered_energy_sum_le (d : Decomposition) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
      ∀ T : Finset ℕ, (∀ t ∈ T, Squarefree t ∧ t ≤ R) →
        (∀ t ∈ T, ∑ p ∈ t.primeFactors, (1 : ℝ)/p ≤ 1/16) →
      ∑ t ∈ T, centeredEnergy (upperWindow d.A (R^2)) (actualSupport d) t ≤
        1536 * (R : ℝ) / ((upperWindow d.A (R^2)).card : ℝ) *
          Real.exp (C * Real.sqrt (Real.log (Real.log (R : ℝ)))) := by
  obtain ⟨C, hC, h⟩ := eventually_actual_centered_energy_budgets d
  exact ⟨C, hC, h.mono (fun R h T hT hcop => (h T hT hcop).1)⟩

theorem eventually_actualB_centered_energy_sum_le (d : Decomposition) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
      ∀ T : Finset ℕ, (∀ t ∈ T, Squarefree t ∧ t ≤ R) →
        (∀ t ∈ T, ∑ p ∈ t.primeFactors, (1 : ℝ)/p ≤ 1/16) →
      ∑ t ∈ T, centeredEnergy (upperWindow d.B (R^2)) (actualSecondSupport d) t ≤
        1536 * (R : ℝ) / ((upperWindow d.B (R^2)).card : ℝ) *
          Real.exp (C * Real.sqrt (Real.log (Real.log (R : ℝ)))) := by
  obtain ⟨C, hC, h⟩ := eventually_actual_centered_energy_budgets d
  exact ⟨C, hC, h.mono (fun R h T hT hcop => (h T hT hcop).2)⟩

end Ostmann.Supply

end

end OAI
