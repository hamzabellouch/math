import OAI.Combinatorics.EditApproximation.Binary.BinaryGatheredValues
import OAI.Combinatorics.EditApproximation.Binary.BinaryLoopSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Stored key/value words and the actual linear lookup call tree. Reads
return pointers to retained words; only comparison scratch is fresh. -/

namespace EditApproximation.BinaryFraction

def storedCells (word : BinaryFraction) : ℕ :=
  word.numerator.bits.length + word.denominator.length + 1

def bufferCells {κ : Type*} (code : κ → ℕ) (keys : List κ) (values : List BinaryFraction) : ℕ :=
  (keys.map fun key => Nat.size (code key) + 1).sum +
    (values.map fun value => storedCells value + 1).sum

theorem storedCells_le_width (word : BinaryFraction) : storedCells word ≤ 2 * word.width + 1 := by
  have hn : word.numerator.bits.length ≤ word.width := le_max_left _ _
  have hd : word.denominator.length ≤ word.width := le_max_right _ _
  unfold storedCells
  omega

theorem bufferCells_le {κ : Type*} (code : κ → ℕ) (keys : List κ) (values : List BinaryFraction)
    (B : ℕ) (hk : ∀ key ∈ keys, Nat.size (code key) ≤ B)
    (hv : ∀ value ∈ values, value.width ≤ B) :
    bufferCells code keys values ≤ keys.length * (B + 1) + values.length * (2 * B + 2) := by
  have hkeys := sum_map_le_length_mul keys (fun key => Nat.size (code key) + 1) (B + 1)
    (fun key hkey => Nat.add_le_add_right (hk key hkey) 1)
  have hvalues := sum_map_le_length_mul values (fun value => storedCells value + 1) (2 * B + 2)
    (fun value hvalue => by have h := storedCells_le_width value; have hb := hv value hvalue; omega)
  unfold bufferCells
  omega

theorem bufferCells_le_fourthPower {κ : Type*} (code : κ → ℕ)
    (keys : List κ) (values : List BinaryFraction) (B X : ℕ)
    (hX : 4 ≤ X) (hk : ∀ key ∈ keys, Nat.size (code key) ≤ B)
    (hv : ∀ value ∈ values, value.width ≤ B)
    (hkeys : keys.length ≤ X) (hvalues : values.length ≤ X) (hB : B ≤ X) :
    bufferCells code keys values ≤ X ^ 4 := by
  have h := bufferCells_le code keys values B hk hv
  have h1 := Nat.mul_le_mul hkeys (Nat.add_le_add_right hB 1)
  have h2 := Nat.mul_le_mul hvalues (show 2 * B + 2 ≤ 2 * X + 2 by omega)
  have hsmall : keys.length * (B + 1) + values.length * (2 * B + 2) ≤ 4 * X ^ 2 := by
    nlinarith only [hX, h1, h2]
  have hsq : 4 ≤ X ^ 2 := by nlinarith only [hX]
  exact h.trans (hsmall.trans (by
    calc
      4 * X ^ 2 ≤ X ^ 2 * X ^ 2 := Nat.mul_le_mul_right _ hsq
      _ = X ^ 4 := by ring))



def gatheredLookupInvocations {κ : Type*} (equal : κ → κ → Bool × ℕ)
    (invocations : κ → κ → ℕ) : List κ → List BinaryFraction → κ → ℕ
  | key :: keys, _value :: values, query =>
    invocations query key + if (equal query key).1 then 1
      else gatheredLookupInvocations equal invocations keys values query + 1
  | _, _, _ => 1

theorem gatheredLookupAllocation_le_work {κ : Type*} (equal : κ → κ → Bool × ℕ)
    (allocation : κ → κ → ℕ) (keys : List κ) (values : List BinaryFraction) (query : κ)
    (h : ∀ key ∈ keys, allocation query key ≤ (equal query key).2) :
    gatheredLookupAllocation equal allocation keys values query ≤
      (gatheredWordLookupWithWork equal keys values query).2 := by
  induction keys generalizing values with
  | nil => exact Nat.zero_le 1
  | cons key keys ih =>
    cases values with
    | nil => exact Nat.zero_le 1
    | cons value values =>
      have hc := h key List.mem_cons_self
      have ht := ih values (fun k hk => h k (List.mem_cons_of_mem _ hk))
      unfold gatheredLookupAllocation gatheredWordLookupWithWork
      dsimp only
      split_ifs <;> dsimp only
      · exact Nat.add_le_add hc (Nat.zero_le 1)
      · exact (Nat.add_le_add hc ht).trans (Nat.le_succ _)

theorem gatheredLookupInvocations_le_work {κ : Type*} (equal : κ → κ → Bool × ℕ)
    (invocations : κ → κ → ℕ) (keys : List κ) (values : List BinaryFraction) (query : κ)
    (h : ∀ key ∈ keys, invocations query key ≤ (equal query key).2) :
    gatheredLookupInvocations equal invocations keys values query ≤
      (gatheredWordLookupWithWork equal keys values query).2 := by
  induction keys generalizing values with
  | nil => rfl
  | cons key keys ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      have hc := h key List.mem_cons_self
      have ht := ih values (fun k hk => h k (List.mem_cons_of_mem _ hk))
      unfold gatheredLookupInvocations gatheredWordLookupWithWork
      dsimp only
      split_ifs <;> dsimp only <;> omega

end EditApproximation.BinaryFraction

end OAI
