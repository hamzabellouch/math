import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.GraphTables
import OAI.Combinatorics.IndependentSets.PCP.GenericGraphTables

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GraphTableComplexity

open IndependentSetsGames.Foundations.Complexity
open Polynomial

noncomputable def encodingPolynomial (q : Nat) : Polynomial Nat :=
  X ^ 2 + C (2 * (q * q) + 1) * X + C 2

theorem encodingPolynomial_eval (q n : Nat) :
    (encodingPolynomial q).eval n = n ^ 2 + (2 * (q * q) + 1) * n + 2 := by
  simp [encodingPolynomial]

theorem encodingPolynomial_mono (q : Nat) {n m : Nat} (hnm : n ≤ m) :
    (encodingPolynomial q).eval n ≤ (encodingPolynomial q).eval m := by
  rw [encodingPolynomial_eval, encodingPolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.pow_le_pow_left hnm 2) (Nat.mul_le_mul_left _ hnm)) 2

theorem rowBound_le_polynomial (q vertices darts : Nat) :
    vertices + darts + 2 + darts * (vertices + darts + 2 * (q * q)) ≤
      (encodingPolynomial q).eval (vertices + darts) := by
  have hd : darts ≤ vertices + darts := Nat.le_add_left darts vertices
  calc
    _ ≤ vertices + darts + 2 +
        (vertices + darts) * (vertices + darts + 2 * (q * q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
    _ = _ := by rw [encodingPolynomial_eval]; ring

theorem generic_size_add_two_le_bits {q : Nat} (table : GenericGraphTables.Table q) :
    table.vertices + table.darts + 2 ≤ (GenericGraphTables.tableBits table).length := by
  simp only [GenericGraphTables.tableBits, GenericGraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

theorem generic_bits_le_polynomial {q : Nat} (table : GenericGraphTables.Table q) :
    (GenericGraphTables.tableBits table).length ≤
      (encodingPolynomial q).eval (table.vertices + table.darts) :=
  (GenericGraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial q table.vertices table.darts)

theorem generic_bits_le_of_size_le {q N : Nat} (table : GenericGraphTables.Table q)
    (hsize : table.vertices + table.darts ≤ N) :
    (GenericGraphTables.tableBits table).length ≤ (encodingPolynomial q).eval N :=
  (generic_bits_le_polynomial table).trans (encodingPolynomial_mono q hsize)

theorem size_add_two_le_bits (table : GraphTables.Table) :
    table.vertices + table.darts + 2 ≤ (GraphTables.tableBits table).length := by
  simp only [GraphTables.tableBits, GraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

theorem bits_le_polynomial (table : GraphTables.Table) :
    (GraphTables.tableBits table).length ≤
      (encodingPolynomial 64).eval (table.vertices + table.darts) :=
  (GraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial 64 table.vertices table.darts)

theorem bits_le_of_size_le {N : Nat} (table : GraphTables.Table)
    (hsize : table.vertices + table.darts ≤ N) :
    (GraphTables.tableBits table).length ≤ (encodingPolynomial 64).eval N :=
  (bits_le_polynomial table).trans (encodingPolynomial_mono 64 hsize)

end IndependentSetsGames.Foundations.PCP.GraphTableComplexity

end OAI
