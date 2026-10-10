import Mathlib
import OAI.Computability.MaxCut.Encoding.FormulaEncoding

namespace OAI

/-!
Bit-length bounds for the concrete unique-game serialization. Every stored
constraint occurrence and every entry of its forward permutation table is
encoded. These are output-size bounds, not machine running-time bounds.
-/

namespace MaxCutGames.Reduction.GameEncodingSize

open Foundations.Target Foundations.Complexity

/-- The full table has `q` labels, each with unary encoding length at most `q+1`.
The conservative bound remains valid when the alphabet is empty. -/
theorem tableBits_length_le {q : Nat} (table : PermutationTable q) :
    (encodeWords (tableWords table)).length ≤ q * (q + 1) := by
  have h := encodeWords_length_le (tableWords table) q (by
    intro value hvalue
    obtain ⟨label, _, hlabel⟩ := List.mem_map.mp hvalue
    rw [← hlabel]
    exact Nat.le_of_lt label.isLt)
  simpa only [tableWords_length] using h

/-- Both endpoint words use at most `n` bits, and the entire forward table is
retained. A constraint itself supplies the endpoint bounds, even for small `n`. -/
theorem constraintBits_length_le {n q : Nat} (constraint : Constraint n q) :
    (encodeWords (constraintWords constraint)).length ≤ 2 * n + q * (q + 1) := by
  have hs := constraint.source.isLt
  have ht := constraint.target.isLt
  have hp := tableBits_length_le constraint.permutation
  simp only [constraintWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

/-- Each occurrence contributes its own complete encoding; no deduplication
or implicit edge weights enter the bound. The empty list is also covered. -/
theorem constraintsBits_length_le {n q : Nat} (constraints : List (Constraint n q)) :
    (encodeWords (constraints.flatMap constraintWords)).length ≤
      constraints.length * (2 * n + q * (q + 1)) := by
  induction constraints with
  | nil => simp [encodeWords]
  | cons constraint constraints ih =>
      have hc := constraintBits_length_le constraint
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Exact header accounting plus a bound on every serialized occurrence.
No lower bound on the alphabet or vertex count is assumed. -/
theorem gameBits_length_le {q : Nat} (g : Instance q) :
    (gameBits g).length ≤
      g.vertices + q + g.constraints.length + 3 +
        g.constraints.length * (2 * g.vertices + q * (q + 1)) := by
  have h := constraintsBits_length_le g.constraints
  simp only [gameBits, gameWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end MaxCutGames.Reduction.GameEncodingSize

end OAI
