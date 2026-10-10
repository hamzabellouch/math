import OAI.Combinatorics.EditApproximation.Binary.IntegerBinaryOutput
import OAI.Combinatorics.EditApproximation.Refinement.ComputedOutputWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQuerySetup

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

/-- Full integer-input runtime with concrete local, setup, and final-output routines. -/
noncomputable def integerBinaryWork (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction) :=
  computedFullOutputWork (source.map integerSymbolCode) (target.map integerSymbolCode) N
    (integerQueryLocalWork source target N) (integerPreevaluationWork source target N epsilon)
    (computedQuerySetupWithWork N).2 (fun input => (integerBinaryOutput source target N input).2)
    (N + 1)

theorem integerBinaryWork_expected_near_linear (C : ℕ) (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (epsilonTime : ℝ) (htime : 0 < epsilonTime) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      (∫ outcome, integerBinaryWork source target N epsilon outcome
        ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
          (N + 2 : ℝ) ^ (1 + epsilonTime) := by
  have hh : 0 < epsilonTime / 2 := half_pos htime
  filter_upwards [physicalLargeInput_eventually epsilon hepsilon,
    integerPreevaluationWork_near_linear C (epsilonTime / 2) hh,
    computedExecutionTotalWork_expected_near_linear computedQueryWorkDegree (epsilonTime / 2) hh,
    integerQueryLocalWork_cap C, integer_encoded_symbol_bits C,
    fixed_height_power_subpolynomial 12 (1 + epsilonTime / 2) (by linarith),
    constant_le_rpow_eventually 5 (epsilonTime / 2) hh] with N hlarge hpre hwork hcap hsymbols hpower hfive
  intro source target hsize halphabet
  have hN := largeAccuracyInput_pos N epsilon.value hlarge.2.1
  have hsetup := computedQuerySetupWithWork_cost N hN hlarge.2.1.1
  have hs : ((computedQuerySetupWithWork N).2 : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := by
    have hc : ((computedQuerySetupWithWork N).2 : ℝ) ≤ (inputHeight N : ℝ) ^ 12 := by
      exact_mod_cast hsetup
    exact hc.trans hpower
  have hten : (inputHeight N : ℝ) ^ 10 ≤ (N + 2 : ℝ) ^ (1 + epsilonTime / 2) :=
    (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ inputHeight N from Nat.one_le_pow _ _ (by decide)))
      (by decide : 10 ≤ 12)).trans hpower
  have hn : (N : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := by
    calc
      _ ≤ (N + 2 : ℝ) := le_add_of_nonneg_right (by norm_num)
      _ = (N + 2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N + 2 : ℝ) ^ (1 + epsilonTime / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by linarith)
  have hf (input) : ((integerBinaryOutput source target N input).2 : ℝ) ≤
      2 * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := by
    have hb := integerBinaryOutput_cost source target N epsilon hlarge hsize input
    have hbR : ((integerBinaryOutput source target N input).2 : ℝ) ≤ N + (inputHeight N : ℝ) ^ 10 := by
      exact_mod_cast hb
    linarith only [hbR, hn, hten]
  have hw := hwork (source.map integerSymbolCode) (target.map integerSymbolCode)
    (by simpa only [List.length_map] using hsize) (hsymbols source target halphabet)
    (integerQueryLocalWork source target N) (hcap source target hsize halphabet)
  have hfull := computedFullOutputWork_expected_le (source.map integerSymbolCode) (target.map integerSymbolCode) N
    (integerQueryLocalWork source target N) (integerPreevaluationWork source target N epsilon)
    (computedQuerySetupWithWork N).2 (fun input => (integerBinaryOutput source target N input).2) (N + 1)
    epsilon hlarge ((N + 2 : ℝ) ^ (1 + epsilonTime / 2))
    (2 * (N + 2 : ℝ) ^ (1 + epsilonTime / 2)) hw hf
  have hp := hpre source target hsize halphabet epsilon
  calc
    _ ≤ (integerPreevaluationWork source target N epsilon : ℝ) + (computedQuerySetupWithWork N).2 +
        (N + 2 : ℝ) ^ (1 + epsilonTime / 2) + 2 * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := hfull
    _ ≤ 5 * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := by linarith only [hp, hs]
    _ ≤ (N + 2 : ℝ) ^ (epsilonTime / 2) * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) :=
      mul_le_mul_of_nonneg_right hfive (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
