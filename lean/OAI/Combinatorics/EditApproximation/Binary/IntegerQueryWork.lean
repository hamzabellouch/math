import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryWork
import OAI.Combinatorics.EditApproximation.Binary.IntegerKernelWork

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

/-- The actual computed widths of the encoded input index. -/
theorem integerQueryWidths (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      integerInputSymbolBits source target ≤ inputHeight N ^ 3 ∧
      integerInputPositionBits target ≤ inputHeight N ^ 3 := by
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop (max 100 C))] with N hlarge
  intro source target hsize halphabet
  have hH : 100 ≤ inputHeight N := (le_max_left _ _).trans (hlarge.trans (computed_smallLog_le_height N))
  have hC : C ≤ inputHeight N := (le_max_right _ _).trans (hlarge.trans (computed_smallLog_le_height N))
  have hs := integerInputSymbolBits_polynomial source target N C halphabet
  have hN := input_length_bits_le N
  have hm := Nat.mul_le_mul hC hN
  have hc : inputHeight N * (inputHeight N + 1) + 3 ≤ inputHeight N ^ 3 := by
    have h := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 3 ≤ inputHeight N by omega)
    nlinarith only [hH, h]
  refine ⟨by omega, ?_⟩
  exact (Nat.size_le_size (show target.length ≤ N from by omega)).trans
    ((computed_input_size_le_height N).trans (Nat.le_pow (by decide)))

def integerQueryLocalWork (source target : List ℤ) (N : ℕ) :=
  computedQueryLocalWork (source.map integerSymbolCode) (target.map integerSymbolCode) N
    (integerOccurrenceIndex source target) (integerInputSymbolBits source target) (integerInputPositionBits target)

theorem integerQueryLocalWork_cap (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ input key, integerQueryLocalWork source target N input key ≤
        computedLocalKernelBudget computedQueryWorkDegree N := by
  filter_upwards [computedQueryLocalWork_cap, integerQueryWidths C] with N hwork hwidth
  intro source target hsize halphabet input key
  have hw := hwidth source target hsize halphabet
  apply hwork (source.map integerSymbolCode) (target.map integerSymbolCode)
    (by simpa only [List.length_map] using hsize) input (integerOccurrenceIndex source target)
    (integerInputSymbolBits source target) (integerInputPositionBits target) hw.1 hw.2
    ?_ ?_ ?_ rfl key
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_left _ hz)
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_right _ hz)
  · simpa only [List.length_map, integerInputPositionBits] using (Nat.lt_size_self target.length).le

/-- Complete integer-input cost with the proved local program, rather than an
unspecified per-key annotation. -/
noncomputable def integerQueryWork (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction) :=
  integerFullKernelWork source target N epsilon (integerQueryLocalWork source target N)

theorem integerQueryWork_expected_near_linear (C : ℕ) (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (epsilonTime : ℝ) (htime : 0 < epsilonTime) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      (∫ outcome, integerQueryWork source target N epsilon outcome
        ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
          (N + 2 : ℝ) ^ (1 + epsilonTime) := by
  filter_upwards [integerFullKernelWork_expected_near_linear C computedQueryWorkDegree
    epsilon hepsilon epsilonTime htime, integerQueryLocalWork_cap C] with N hwork hcap
  intro source target hsize halphabet
  exact hwork source target hsize halphabet (integerQueryLocalWork source target N)
    (hcap source target hsize halphabet)

end EditApproximation

end OAI
