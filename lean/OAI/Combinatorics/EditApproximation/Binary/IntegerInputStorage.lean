import OAI.Combinatorics.EditApproximation.Coarse.CoarseInputStorage
import OAI.Combinatorics.EditApproximation.Binary.IntegerCoarseSymbolBits
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter

/-- A sign field, magnitude bits and one pointer/header word per input symbol. -/


theorem storedIntegerBits_le (values : List ℤ) (A : ℕ)
    (h : ∀ z ∈ values, z.natAbs ≤ A) :
    storedIntegerBits values ≤ 1 + values.length * (A + 2) := by
  have hs : (values.map fun z => Nat.size z.natAbs + 2).sum ≤ values.length * (A + 2) := by
    induction values with
    | nil => simp
    | cons z values ih =>
      have hz : Nat.size z.natAbs ≤ A :=
        (Nat.size_le.mpr z.natAbs.lt_two_pow_self).trans (h z List.mem_cons_self)
      have ht := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  exact Nat.add_le_add_left hs 1

private theorem pair_storage_power (X C nx ny sx sy : ℕ) (hX : 2 ≤ X)
    (hn : nx + ny ≤ X) (hs : sx ≤ 1 + nx * (X ^ C + 2))
    (ht : sy ≤ 1 + ny * (X ^ C + 2)) : sx + sy ≤ X ^ (C + 3) := by
  have hp : 1 ≤ X ^ C := one_le_pow₀ (by omega)
  have hc : 4 ≤ X ^ 2 := by nlinarith only [hX]
  calc
    _ ≤ 2 + (nx + ny) * (X ^ C + 2) := by nlinarith only [hs, ht]
    _ ≤ 4 * X * X ^ C := by
      have hm := Nat.mul_le_mul_right (X ^ C + 2) hn
      nlinarith only [hm, hX, Nat.mul_le_mul_left X hp]
    _ ≤ X ^ 2 * X * X ^ C := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right X hc)
    _ = X ^ (C + 3) := by rw [pow_add]; ring

theorem storedIntegerInput_polynomial (source target : List ℤ) (N C : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    storedIntegerBits source + storedIntegerBits target ≤ (N + 2) ^ (C + 3) := by
  exact pair_storage_power (N + 2) C source.length target.length
    (storedIntegerBits source) (storedIntegerBits target) (by omega) (by omega)
    (storedIntegerBits_le source _ (fun z hz => hsymbol z (List.mem_append_left _ hz)))
    (storedIntegerBits_le target _ (fun z hz => hsymbol z (List.mem_append_right _ hz)))

end EditApproximation

end OAI
