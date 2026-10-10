import OAI.Combinatorics.BinaryEdit.Model
import Mathlib.Tactic

namespace OAI

/-! Indexing fixed-width concatenated codewords. -/
namespace TreeEdit.BinaryLower

universe u v
variable {α : Type u} {β : Type v} {P : ℕ}

/-- A block-coordinate lookup in the actual concatenation extension. -/
theorem getElem?_encode_block (c : α → Word β P) (x : List α)
    (i j : ℕ) (hi : i < x.length) (hj : j < P) :
    (encode c x)[i * P + j]? = (c x[i]).val[j]? := by
  induction x generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons a x ih =>
      cases i with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero, encode,
            List.flatMap_cons]
          exact List.getElem?_append_left (by simpa only [(c a).property] using hj)
      | succ i =>
          have hi' : i < x.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
          simp only [encode, List.flatMap_cons, List.getElem_cons_succ]
          rw [List.getElem?_append_right (by rw [(c a).property]; simp only [Nat.add_mul, Nat.one_mul]; omega)]
          rw [(c a).property]
          have heq : (i + 1) * P + j - P = i * P + j := by
            simp only [Nat.add_mul, Nat.one_mul]
            omega
          rw [heq]
          exact ih i hi'

/-- Any encoded position is found by its quotient block and remainder offset. -/
theorem getElem?_encode_quotient (c : α → Word β P) (x : List α)
    (k : ℕ) (hP : 0 < P) (hk : k / P < x.length) :
    (encode c x)[k]? = (c x[k / P]).val[k % P]? := by
  have h := getElem?_encode_block c x (k / P) (k % P) hk (Nat.mod_lt k hP)
  simpa only [Nat.div_add_mod'] using h

/-- The total lookup counterpart of `getElem?_encode_block`. -/
theorem getElem_encode_block (c : α → Word β P) (x : List α)
    (i j : ℕ) (hi : i < x.length) (hj : j < P)
    (hbit : i * P + j < (encode c x).length) :
    (encode c x)[i * P + j] =
      (c x[i]).val[j]'(by rw [(c x[i]).property]; exact hj) := by
  have h := getElem?_encode_block c x i j hi hj
  simpa only [List.getElem?_eq_getElem hbit,
    List.getElem?_eq_getElem (by rw [(c x[i]).property]; exact hj), Option.some.injEq] using h

/-- Total lookup at an arbitrary encoded position. -/
theorem getElem_encode_quotient (c : α → Word β P) (x : List α)
    (k : ℕ) (hP : 0 < P) (hk : k / P < x.length)
    (hbit : k < (encode c x).length) :
    (encode c x)[k] =
      (c x[k / P]).val[k % P]'(by rw [(c x[k / P]).property]; exact Nat.mod_lt k hP) := by
  have h := getElem?_encode_quotient c x k hP hk
  simpa only [List.getElem?_eq_getElem hbit,
    List.getElem?_eq_getElem (by rw [(c x[k / P]).property]; exact Nat.mod_lt k hP),
    Option.some.injEq] using h

/-- A segment wholly contained in one encoded block is exactly the
corresponding segment of that codeword. -/
theorem encode_segment_eq (c : α → Word β P) (x : List α)
    (i j a : ℕ) (hi : i < x.length) (hja : j + a ≤ P) :
    ((encode c x).drop (i * P + j)).take a =
      (((c x[i]).val).drop j).take a := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a
  · have hjk : j + k < P := by omega
    simpa only [List.getElem?_take, hk, ite_true, List.getElem?_drop,
      Nat.add_assoc] using getElem?_encode_block c x i (j + k) hi hjk
  · simp only [List.getElem?_take, hk, ite_false]

/-- The same segment identity with start specified as one global index. -/
theorem encode_segment_quotient_eq (c : α → Word β P) (x : List α)
    (k a : ℕ) (hk : k / P < x.length) (hka : k % P + a ≤ P) :
    ((encode c x).drop k).take a =
      (((c x[k / P]).val).drop (k % P)).take a := by
  simpa only [Nat.div_add_mod'] using
    encode_segment_eq c x (k / P) (k % P) a hk hka

end TreeEdit.BinaryLower

end OAI
