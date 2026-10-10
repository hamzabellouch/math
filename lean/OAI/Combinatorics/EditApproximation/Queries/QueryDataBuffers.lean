import OAI.Combinatorics.EditApproximation.Queries.QuerySourceBuffers
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Counted local data buffers for the adaptive gathers. Bounds depend on
stored keys and the requested key, not on an unbounded ambient key type. -/

namespace EditApproximation
namespace BinaryFraction

theorem gatheredWordLookupWithWork_cost_on {κ : Type*}
    (equal : κ → κ → Bool × ℕ) (C : ℕ) (keys : List κ)
    (values : List BinaryFraction) (query : κ)
    (hC : ∀ key ∈ keys, (equal query key).2 ≤ C) :
    (gatheredWordLookupWithWork equal keys values query).2 ≤
      1 + keys.length * (C + 1) := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_rfl]
  | cons key keys ih =>
    have hc := hC key List.mem_cons_self
    have ht := ih (values.drop 1) (fun k hk => hC k (List.mem_cons_of_mem _ hk))
    cases values with
    | nil => simp only [gatheredWordLookupWithWork]; omega
    | cons value values =>
      simp only [List.drop_succ_cons, List.drop_zero] at ht
      simp only [gatheredWordLookupWithWork]
      split_ifs <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega



@[simp] theorem queryChildReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × TargetInterval n)) (values : List BinaryFraction)
    (i : Fin M) (q : TargetInterval n) :
    (queryChildReadWithWork keys values i q).1.value =
      finiteAnswerTable keys (values.map value) (i, q) :=
  gatheredWordLookupWithWork_value _ coordinateEqualWithWork_value keys values (i, q)

theorem queryChildReadWithWork_cost {M n : ℕ} (keys : List (Fin M × TargetInterval n))
    (values : List BinaryFraction) (i : Fin M) (q : TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryChildReadWithWork keys values i q).2 ≤ 1 + keys.length * (24 * B + 9) := by
  exact gatheredWordLookupWithWork_cost coordinateEqualWithWork (24 * B + 8)
    (fun a b => coordinateEqualWithWork_cost a b B hM hn) keys values (i, q)



@[simp] theorem queryHistoryReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) :
    (queryHistoryReadWithWork keys values s input).1.value =
      finiteAnswerTable keys (values.map value) (input.1, s, input.2) :=
  gatheredWordLookupWithWork_value _ queryHistoryEqualWithWork_value keys values (input.1, s, input.2)

theorem queryHistoryReadWithWork_cost {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) (B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) (hs : Nat.size s ≤ B)
    (ht : ∀ key ∈ keys, Nat.size key.2.1 ≤ B) :
    (queryHistoryReadWithWork keys values s input).2 ≤
      1 + keys.length * (32 * B + 12) := by
  apply gatheredWordLookupWithWork_cost_on queryHistoryEqualWithWork (32 * B + 11)
  intro key hk
  have hc := coordinateEqualWithWork_cost input (key.1, key.2.2) B hM hn
  have he := naturalEqualWithWork_cost s key.2.1 B hs (ht key hk)
  change (coordinateEqualWithWork input (key.1, key.2.2)).2 +
    (naturalEqualWithWork s key.2.1).2 + 1 ≤ _
  omega

theorem queryHistoryReadWithWork_width {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) (B : ℕ)
    (hB : 2 ≤ B) (hv : ∀ v ∈ values, v.width ≤ B) :
    (queryHistoryReadWithWork keys values s input).1.width ≤ B :=
  gatheredWordLookupWithWork_width _ keys values _ B hB hv

end BinaryFraction
end EditApproximation

end OAI
