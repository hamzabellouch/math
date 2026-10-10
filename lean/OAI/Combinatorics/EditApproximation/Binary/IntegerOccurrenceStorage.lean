import OAI.Combinatorics.EditApproximation.Geometry.OccurrenceStorage
import OAI.Combinatorics.EditApproximation.Binary.IntegerOccurrenceIndex
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter

/-- Actual counters and trie nodes of the encoded target occurrence index. -/


theorem integerOccurrenceStorage_bound (source target : List ℤ) (N C : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    integerOccurrenceStorage source target ≤ 9 * (C + 2) * (N + 2) ^ 5 := by
  have h := occurrenceBuild_storage (integerInputSymbolBits source target)
    (integerInputPositionBits target) ((target.map integerSymbolCode).zipIdx)
  simp only [List.length_zipIdx, List.length_map] at h
  change integerOccurrenceStorage source target ≤ _ at h
  let X := N + 2
  have hX : 2 ≤ X := by dsimp only [X]; omega
  have hn : target.length ≤ X := by dsimp only [X]; omega
  have hsz : Nat.size target.length ≤ X :=
    (Nat.size_le_size hn).trans (Nat.size_le.mpr X.lt_two_pow_self)
  have hp : integerInputPositionBits target + 1 ≤ 2 * X := by
    change Nat.size target.length + 1 ≤ 2 * X
    omega
  have hs : integerInputSymbolBits source target + 1 ≤ (C + 2) * X := by
    have hs := integerInputSymbolBits_polynomial source target N C hsymbol
    have hb : Nat.size (N + 2) ≤ X := Nat.size_le.mpr X.lt_two_pow_self
    nlinarith only [hs, hb, hX]
  have hcounter : Nat.size target.length + 3 ≤ 3 * X := by omega
  have hpos := Nat.mul_le_mul hn hp
  have htree := Nat.mul_le_mul hcounter hpos
  have hdict := Nat.mul_le_mul hn hs
  have hunit : 1 ≤ X ^ 3 := one_le_pow₀ (by omega)
  have hv : (Nat.size target.length + 3) * (target.length *
      (integerInputPositionBits target + 1)) + 3 ≤ 9 * X ^ 3 := by
    nlinarith only [htree, hunit]
  calc
    _ ≤ ((Nat.size target.length + 3) * (target.length *
        (integerInputPositionBits target + 1)) + 3) *
        (target.length * (integerInputSymbolBits source target + 1)) := h
    _ ≤ (9 * X ^ 3) * (X * ((C + 2) * X)) := Nat.mul_le_mul hv hdict
    _ = _ := by ring

theorem integerOccurrenceStorage_polynomial (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      integerOccurrenceStorage source target ≤ (N + 2) ^ 6 := by
  filter_upwards [eventually_ge_atTop (9 * (C + 2))] with N hN
  intro source target hsize hsymbol
  calc
    _ ≤ 9 * (C + 2) * (N + 2) ^ 5 :=
      integerOccurrenceStorage_bound source target N C hsize hsymbol
    _ ≤ (N + 2) * (N + 2) ^ 5 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end EditApproximation

end OAI
