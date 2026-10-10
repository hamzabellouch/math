import OAI.Combinatorics.EditApproximation.Binary.IntegerInputStorage
import OAI.Combinatorics.EditApproximation.Binary.IntegerOccurrenceStorage
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter

private theorem natural_pair_storage (source target : List ℕ) (X A : ℕ)
    (hX : 2 ≤ X) (hsize : source.length + target.length ≤ X)
    (hwidth : ∀ a ∈ source ++ target, Nat.size a ≤ X ^ A) :
    storedNaturalBits source + storedNaturalBits target ≤ X ^ (A + 3) := by
  have hs := storedNaturalBits_le source (X ^ A)
    (fun a ha => hwidth a (List.mem_append_left _ ha))
  have ht := storedNaturalBits_le target (X ^ A)
    (fun a ha => hwidth a (List.mem_append_right _ ha))
  have hp : 1 ≤ X ^ A := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul_right (X ^ A + 1) hsize
  have hc : 4 ≤ X ^ 2 := by nlinarith only [hX]
  calc
    _ ≤ 4 * X * X ^ A := by nlinarith only [hs, ht, hm, hX, Nat.mul_le_mul_left X hp]
    _ ≤ X ^ 2 * X * X ^ A := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right X hc)
    _ = _ := by rw [pow_add]; ring

theorem storedNaturalInput_polynomial (source target : List ℕ) (N : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) :
    storedNaturalBits source + storedNaturalBits target ≤ (N + 2) ^ 15 := by
  have hh := Nat.pow_le_pow_left (computed_height_polynomial N) 3
  rw [← pow_mul] at hh
  exact natural_pair_storage source target (N + 2) 12 (by omega) (by omega)
    (fun a ha => (hsymbol a ha).trans hh)

/-- The explicitly retained original integer input, its encoded arrays,
and the target occurrence index. -/


private theorem combine_input_storage (X C raw encoded index : ℕ) (hX : 2 ≤ X)
    (hr : raw ≤ X ^ (C + 3)) (he : encoded ≤ X ^ 15) (hi : index ≤ X ^ 6) :
    raw + encoded + index ≤ X ^ (C + 22) := by
  let K := C + 20
  have hpos : 0 < X := by omega
  have hr' : raw ≤ X ^ K := hr.trans (Nat.pow_le_pow_right hpos (by dsimp only [K]; omega))
  have he' : encoded ≤ X ^ K := he.trans (Nat.pow_le_pow_right hpos (by dsimp only [K]; omega))
  have hi' : index ≤ X ^ K := hi.trans (Nat.pow_le_pow_right hpos (by dsimp only [K]; omega))
  calc
    _ ≤ 3 * X ^ K := by omega
    _ ≤ X ^ 2 * X ^ K := Nat.mul_le_mul_right _ (by nlinarith only [hX])
    _ = _ := by rw [← pow_add]; congr 1; dsimp only [K]; omega

theorem integerStoredDataSpace_polynomial (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      integerStoredDataSpace source target ≤ (N + 2) ^ (C + 22) := by
  filter_upwards [integer_encoded_symbol_bits C, integerOccurrenceStorage_polynomial C]
    with N hbits hindex
  intro source target hsize hsymbols
  have hr := storedIntegerInput_polynomial source target N C hsize hsymbols
  have he := storedNaturalInput_polynomial (source.map integerSymbolCode)
    (target.map integerSymbolCode) N (by simpa only [List.length_map] using hsize)
    (hbits source target hsymbols)
  have hi := hindex source target hsize hsymbols
  have h := combine_input_storage (N + 2) C _ _ _ (by omega) hr he hi
  unfold integerStoredDataSpace
  omega

end EditApproximation

end OAI
