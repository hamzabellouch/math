import OAI.Combinatorics.EditApproximation.Refinement.ComputedFamilyEncoding
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation







 theorem computedFamilyMemoCode_injective (source target : List ℕ) (N R : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    Function.Injective (computedFamilyMemoCode source target N R) := by
  have hM : 1 ≤ (integerParameters N).M := (by omega : 1 ≤ 2).trans
    (computed_branching_bounds N hN hell).1
  exact SourceRanked.keyCode_injective _ _
    (physicalFamilyCode_injective target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) hM)
    (ChargedPhysicalRequest.code_injective hM)

 theorem computedFamilyMemoCode_fits (source target : List ℕ) (N R : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
    computedFamilyMemoCode source target N R key < 2 ^ (16384 * inputHeight N + 5) := by
  have hM : 1 ≤ (integerParameters N).M := (by omega : 1 ≤ 2).trans
    (computed_branching_bounds N hN (by omega)).1
  have hH : 2 ≤ inputHeight N := (by omega : 2 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hpass : computedSeedPassCount N + 1 ≤ inputHeight N ^ 2 := by
    have h := computedSeedPassCount_le_height N hN hell
    nlinarith only [h, hH]
  apply mixedCode_lt_two_pow _ _ (16384 * inputHeight N + 4)
  · intro scalar
    exact computed_physicalFamilyCode_bound N source.length target.length R hN hell
      (by omega) (by omega) hR hB target rfl scalar
  · intro table
    have hb := computed_charged_request_bits_le N source.length target.length
      (computedSeedPassCount N + 1) (inputHeight N ^ 2) hN (by omega) (by omega) (by omega)
      hpass le_rfl
    exact (ChargedPhysicalRequest.code_fits hM table).trans_le
      (Nat.pow_le_pow_right (by decide) (hb.trans (by omega)))

end EditApproximation

end OAI
