import OAI.Combinatorics.EditApproximation.Binary.IntegerKernelWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open MeasureTheory Filter

/-- Execution cost including shared binary setup and the final conversion.
The exact branch keeps its own charged dynamic program. -/


theorem computedFullOutputWork_expected_le (source target : List ℕ) (N : ℕ)
    (cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ)
    (setup : ℝ) (shared : ℕ) (output : ComputedFamilyInput source target N → ℕ)
    (fallbackOutput : ℕ) (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon)
    (budget outputBudget : ℝ)
    (hbudget : (∫ execution, computedExecutionTotalWork source target N cost execution
      ∂computedExecutionLaw source target N) ≤ budget)
    (houtput : ∀ input, (output input : ℝ) ≤ outputBudget) :
    (∫ outcome, computedFullOutputWork source target N cost setup shared output fallbackOutput outcome
      ∂computedFullLaw source target N epsilon) ≤ setup + shared + budget + outputBudget := by
  have hmap := integral_map (μ := computedExecutionLaw source target N)
    measurable_inr.aemeasurable
    (measurable_of_countable
      (computedFullOutputWork source target N cost setup shared output fallbackOutput)).aestronglyMeasurable
  simp only [computedFullLaw, hlarge, ite_true]
  rw [hmap]
  change (∫ execution, (setup + shared) + computedExecutionTotalWork source target N cost execution +
    (output (computedExecutionAccepted source target N execution) : ℝ)
    ∂computedExecutionLaw source target N) ≤ _
  have ho := computedExecutionAcceptedWork_integrable source target N (fun input => (output input : ℝ))
  change Integrable (fun execution => (output (computedExecutionAccepted source target N execution) : ℝ))
    (computedExecutionLaw source target N) at ho
  have ht := computedExecutionTotalWork_integrable source target N cost
  have hconst : Integrable (fun _ : ComputedExecutionOutcome source target N => setup + (shared : ℝ))
      (computedExecutionLaw source target N) := integrable_const _
  have hfirst : Integrable (fun execution => setup + (shared : ℝ) +
      computedExecutionTotalWork source target N cost execution) (computedExecutionLaw source target N) := hconst.add ht
  have hsplit := integral_add hfirst ho
  change (∫ execution, setup + (shared : ℝ) + computedExecutionTotalWork source target N cost execution +
    (output (computedExecutionAccepted source target N execution) : ℝ) ∂computedExecutionLaw source target N) = _ at hsplit
  rw [hsplit]
  have hsplitFirst := integral_add hconst ht
  change (∫ execution, setup + (shared : ℝ) + computedExecutionTotalWork source target N cost execution
    ∂computedExecutionLaw source target N) = _ at hsplitFirst
  rw [hsplitFirst]
  have hb : (∫ execution, (output (computedExecutionAccepted source target N execution) : ℝ)
      ∂computedExecutionLaw source target N) ≤ outputBudget := by
    calc
      _ ≤ ∫ _ : ComputedExecutionOutcome source target N, outputBudget ∂computedExecutionLaw source target N :=
        integral_mono ho (integrable_const _) (fun execution => houtput _)
      _ = outputBudget := by simp
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  linarith only [hbudget, hb]

end EditApproximation

end OAI
