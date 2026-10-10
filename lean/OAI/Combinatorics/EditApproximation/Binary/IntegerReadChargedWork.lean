import OAI.Combinatorics.EditApproximation.Refinement.ComputedReadChargedWork
import OAI.Combinatorics.EditApproximation.Binary.IntegerCoarseSymbolBits
import OAI.Combinatorics.EditApproximation.Refinement.ComputedPreevaluation
import OAI.Combinatorics.EditApproximation.Binary.IntegerAlgorithm

namespace OAI

namespace EditApproximation
open MeasureTheory Filter

noncomputable def computedFullReadChargedWork (source target : List ℕ) (N : ℕ) (setup : ℝ) :
    ComputedFullOutcome source target N → ℝ
  | .inl _ => setup + (chargedSuffixDP source target).2
  | .inr execution => setup + computedExecutionReadChargedWork source target N execution

 theorem computedFullReadChargedWork_expected_le (source target : List ℕ) (N : ℕ)
    (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon) (setup budget : ℝ)
    (hbudget : (∫ execution, computedExecutionReadChargedWork source target N execution
      ∂computedExecutionLaw source target N) ≤ budget) :
    (∫ outcome, computedFullReadChargedWork source target N setup outcome
      ∂computedFullLaw source target N epsilon) ≤ setup + budget := by
  have hmap := integral_map (μ := computedExecutionLaw source target N)
    measurable_inr.aemeasurable
    (measurable_of_countable (computedFullReadChargedWork source target N setup)).aestronglyMeasurable
  simp only [computedFullLaw, hlarge, ite_true]
  rw [hmap]
  change (∫ execution, setup + computedExecutionReadChargedWork source target N execution
    ∂computedExecutionLaw source target N) ≤ setup + budget
  rw [integral_add (integrable_const setup) (computedExecutionReadChargedWork_integrable source target N)]
  simpa [integral_const, add_comm] using add_le_add_left hbudget setup

noncomputable def integerFullReadChargedWork (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction) :
    ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N → ℝ :=
  computedFullReadChargedWork (source.map integerSymbolCode) (target.map integerSymbolCode) N
    (integerPreevaluationWork source target N epsilon)

 theorem integerFullReadChargedWork_expected_near_linear (C : ℕ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (epsilonTime : ℝ) (htime : 0 < epsilonTime) :
    ∀ᶠ N in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      (∫ outcome, integerFullReadChargedWork source target N epsilon outcome
        ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
        (N + 2 : ℝ) ^ (1 + epsilonTime) := by
  have hh : 0 < epsilonTime / 2 := half_pos htime
  filter_upwards [physicalLargeInput_eventually epsilon hepsilon,
    integerPreevaluationWork_near_linear C (epsilonTime / 2) hh,
    computedExecutionReadChargedWork_expected_near_linear (epsilonTime / 2) hh,
    constant_le_rpow_eventually 2 (epsilonTime / 2) hh, integer_encoded_symbol_bits C] with N hlarge hsetup hwork htwo hsymbols
  intro source target hsize halphabet
  have hw := hwork (source.map integerSymbolCode) (target.map integerSymbolCode)
    (by simpa only [List.length_map] using hsize) (hsymbols source target halphabet)
  have hs := hsetup source target hsize halphabet epsilon
  have hf := computedFullReadChargedWork_expected_le (source.map integerSymbolCode)
    (target.map integerSymbolCode) N epsilon hlarge
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
