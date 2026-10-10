import OAI.Combinatorics.EditApproximation.Refinement.ComputedExecutionKernelWork
import OAI.Combinatorics.EditApproximation.Binary.IntegerReadChargedWork

namespace OAI

namespace EditApproximation
open MeasureTheory Filter

/-- Full execution counter: the exact fallback branch or the charged
randomized execution, including its concrete local kernel costs. -/
noncomputable def computedFullKernelWork (source target : List ℕ) (N : ℕ)
    (cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ)
    (setup : ℝ) : ComputedFullOutcome source target N → ℝ
  | .inl _ => setup + (chargedSuffixDP source target).2
  | .inr execution => setup + computedExecutionTotalWork source target N cost execution

theorem computedFullKernelWork_expected_le (source target : List ℕ) (N : ℕ)
    (cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ)
    (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon) (setup budget : ℝ)
    (hbudget : (∫ execution, computedExecutionTotalWork source target N cost execution
      ∂computedExecutionLaw source target N) ≤ budget) :
    (∫ outcome, computedFullKernelWork source target N cost setup outcome
      ∂computedFullLaw source target N epsilon) ≤ setup + budget := by
  have hmap := integral_map (μ := computedExecutionLaw source target N)
    measurable_inr.aemeasurable
    (measurable_of_countable (computedFullKernelWork source target N cost setup)).aestronglyMeasurable
  simp only [computedFullLaw, hlarge, ite_true]
  rw [hmap]
  change (∫ execution, setup + computedExecutionTotalWork source target N cost execution
    ∂computedExecutionLaw source target N) ≤ setup + budget
  rw [integral_add (integrable_const setup) (computedExecutionTotalWork_integrable source target N cost)]
  simpa [integral_const, add_comm] using add_le_add_left hbudget setup

noncomputable def integerFullKernelWork (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction)
    (cost : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N →
      ComputedFamilyMemoKey (source.map integerSymbolCode) (target.map integerSymbolCode) N → ℕ) :
    ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N → ℝ :=
  computedFullKernelWork (source.map integerSymbolCode) (target.map integerSymbolCode) N cost
    (integerPreevaluationWork source target N epsilon)

/-- Runtime transport for the concrete local evaluator, with no additional
probability hypothesis. -/
theorem integerFullKernelWork_expected_near_linear (C D : ℕ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (epsilonTime : ℝ) (htime : 0 < epsilonTime) :
    ∀ᶠ N in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ cost : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N →
        ComputedFamilyMemoKey (source.map integerSymbolCode) (target.map integerSymbolCode) N → ℕ,
      (∀ input key, cost input key ≤ computedLocalKernelBudget D N) →
      (∫ outcome, integerFullKernelWork source target N epsilon cost outcome
        ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
        (N + 2 : ℝ) ^ (1 + epsilonTime) := by
  have hh : 0 < epsilonTime / 2 := half_pos htime
  filter_upwards [physicalLargeInput_eventually epsilon hepsilon,
    integerPreevaluationWork_near_linear C (epsilonTime / 2) hh,
    computedExecutionTotalWork_expected_near_linear D (epsilonTime / 2) hh,
    constant_le_rpow_eventually 2 (epsilonTime / 2) hh, integer_encoded_symbol_bits C]
    with N hlarge hsetup hwork htwo hsymbols
  intro source target hsize halphabet cost hcost
  have hw := hwork (source.map integerSymbolCode) (target.map integerSymbolCode)
    (by simpa only [List.length_map] using hsize) (hsymbols source target halphabet) cost hcost
  have hs := hsetup source target hsize halphabet epsilon
  have hf := computedFullKernelWork_expected_le (source.map integerSymbolCode)
    (target.map integerSymbolCode) N cost epsilon hlarge
    (integerPreevaluationWork source target N epsilon) ((N + 2 : ℝ) ^ (1 + epsilonTime / 2)) hw
  calc
    _ ≤ (integerPreevaluationWork source target N epsilon : ℝ) +
        (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := hf
    _ ≤ 2 * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := by linarith only [hs]
    _ ≤ (N + 2 : ℝ) ^ (epsilonTime / 2) * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
