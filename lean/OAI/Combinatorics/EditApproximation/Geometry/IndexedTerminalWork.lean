import OAI.Combinatorics.EditApproximation.Binary.IntegerPreprocessing
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter

/-- Empty and singleton terminal states use the already prepared occurrence
index. Endpoints are read directly; no target substring is copied. -/


 theorem indexedLeafWithWork_value (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    (indexedLeafWithWork table symbolBits positionBits symbol lo hi).1 =
      indexedLeafCost table symbolBits positionBits symbol lo hi := by
  cases symbol with
  | none => rfl
  | some a => exact (indexedSingletonCostWithWork_spec table symbolBits positionBits a lo hi).1

 theorem indexedLeafWithWork_cost (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    (indexedLeafWithWork table symbolBits positionBits symbol lo hi).2 ≤
      2 * symbolBits + 4 * positionBits + 10 := by
  cases symbol with
  | none => change 2 ≤ _; omega
  | some a => exact (indexedSingletonCostWithWork_spec table symbolBits positionBits a lo hi).2.trans (by omega)

 theorem indexedLeafWithWork_exact (symbolBits positionBits : ℕ) (source target : List ℕ)
    (hsource : ∀ a ∈ source, a < 2 ^ symbolBits)
    (htarget : ∀ a ∈ target, a < 2 ^ symbolBits) (hposition : target.length ≤ 2 ^ positionBits)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ target.length) (hleaf : source.length ≤ 1) :
    (indexedLeafWithWork (occurrenceBuild symbolBits positionBits target.zipIdx)
      symbolBits positionBits source.head? lo hi).1 =
      EditDistortion.edit source (substring target lo hi) := by
  rw [indexedLeafWithWork_value]
  exact indexedLeafCost_exact symbolBits positionBits source target hsource htarget hposition lo hi hlo hhi hleaf

 theorem integerIndexedLeafWithWork_cost (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ symbol lo hi,
        (indexedLeafWithWork (integerOccurrenceIndex source target) (integerInputSymbolBits source target)
          (integerInputPositionBits target) symbol lo hi).2 ≤ inputHeight N ^ 3 := by
  filter_upwards [inputHeight_real_tendsto.eventually (eventually_ge_atTop ((max 100 C : ℕ) : ℝ))] with N hH
  have hH' : max 100 C ≤ inputHeight N := by exact_mod_cast hH
  intro source target hsize halphabet symbol lo hi
  have hs := integerInputSymbolBits_polynomial source target N C halphabet
  have hp : integerInputPositionBits target ≤ Nat.size (N + 2) := Nat.size_le_size (by omega)
  have hn := input_length_bits_le N
  have hc := indexedLeafWithWork_cost (integerOccurrenceIndex source target)
    (integerInputSymbolBits source target) (integerInputPositionBits target) symbol lo hi
  have hCH : C * Nat.size (N + 2) ≤ inputHeight N * (inputHeight N + 1) :=
    Nat.mul_le_mul (by omega) hn
  have h100 : 100 ≤ inputHeight N := by omega
  have hcube : 100 * inputHeight N ^ 2 ≤ inputHeight N ^ 3 := by
    have h := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 100 ≤ inputHeight N by omega)
    nlinarith only [h]
  nlinarith only [hc, hs, hp, hn, hCH, hcube, h100]

end EditApproximation

end OAI
