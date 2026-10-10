import Mathlib.Algebra.Polynomial.Eval.Defs
import OAI.Computability.UniqueGames.PCP.Clone100

namespace OAI

section

namespace UniqueGamesTheorem.Outer.Clone100Encoding

open UniqueGamesTheorem.Reduction CloneGap
open Clone100
open UniqueGamesTheorem.Foundations.Complexity

noncomputable section

def tripleWords (t : Clone100Triples.GoodTriple) : Nat × Nat × Nat :=
  (t.val.1.val, t.val.2.1.val, t.val.2.2.val)

def fixedTriples : List (Nat × Nat × Nat) := Clone100.triples.map tripleWords

theorem fixedTriples_length : fixedTriples.length = 970200 := by
  simp [fixedTriples, Clone100.triples_length]

theorem fixedTriples_properties {t : Nat × Nat × Nat} (ht : t ∈ fixedTriples) :
    t.1 < 100 ∧ t.2.1 < 100 ∧ t.2.2 < 100 ∧
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
  exact ⟨u.val.1.isLt, u.val.2.1.isLt, u.val.2.2.isLt,
    fun h => u.property.1 (Fin.ext h),
    fun h => u.property.2.1 (Fin.ext h),
    fun h => u.property.2.2 (Fin.ext h)⟩

theorem name_value {n : Nat} (v : Fin n) (c : Fin 100) :
    (nameEquiv n (v, c)).val = 100 * v.val + c.val := by
  simp [nameEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

def equationWords {n : Nat} (e : Equation (Fin n)) (t : Nat × Nat × Nat) : List Nat :=
  [100 * e.first.val + t.1, 100 * e.second.val + t.2.1,
    100 * e.third.val + t.2.2, if e.rhs then 1 else 0]

theorem equation_words {n : Nat} (e : Equation (Fin n)) (t : Clone100Triples.GoodTriple) :
    SourceEncoding.equationWords (equation e t) = equationWords e (tripleWords t) := by
  cases h : e.rhs <;>
    simp [SourceEncoding.equationWords, equation, equationWords, tripleWords, name_value, h]

def bodyWords {n : Nat} (es : List (Equation (Fin n))) : List Nat :=
  es.flatMap (fun e => fixedTriples.flatMap (equationWords e))

theorem equations_words {n : Nat} (es : List (Equation (Fin n))) :
    (equations es).flatMap SourceEncoding.equationWords = bodyWords es := by
  simp only [equations, bodyWords, fixedTriples, List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro e _
  apply List.flatMap_congr
  intro t _
  exact equation_words e t

def inputWords (input : SourceEncoding.Input) : List Nat :=
  [input.variables * 100, input.equations.length * 970200] ++ bodyWords input.equations

theorem clonedInput_words (input : SourceEncoding.Input) :
    SourceEncoding.inputWords (clonedInput input) = inputWords input := by
  simp [SourceEncoding.inputWords, clonedInput, inputWords, equations_length, equations_words]

theorem clonedInput_decodes (input : SourceEncoding.Input) :
    SourceEncoding.decodeInputWords (inputWords input) = some (clonedInput input) := by
  rw [← clonedInput_words]
  exact SourceEncoding.decodeInputWords_encoded _

def sizePolynomial : Polynomial Nat :=
  Polynomial.C 100 * Polynomial.X + Polynomial.C 970200 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 970200 * Polynomial.X) * (Polynomial.C 300 * Polynomial.X + Polynomial.C 2)

theorem sizePolynomial_eval (N : Nat) :
    sizePolynomial.eval N = 100 * N + 970200 * N + 2 + 970200 * N * (300 * N + 2) := by
  simp [sizePolynomial]

theorem clonedInput_bits_polynomial (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (clonedInput input)).length ≤
      sizePolynomial.eval (SourceEncoding.inputBits input).length := by
  have hn := SourceEncoding.inputBits_length_ge_variables input
  have hm := SourceEncoding.inputBits_length_ge_equations input
  have ha := Nat.mul_le_mul_right 100 hn
  have hb := Nat.mul_le_mul_right 970200 hm
  have hc := Nat.mul_le_mul_left 300 hn
  have hd := Nat.mul_le_mul hb (Nat.add_le_add_right hc 2)
  apply (Clone100.clonedInput_bits_length_le input).trans
  rw [sizePolynomial_eval]
  nlinarith

end
end UniqueGamesTheorem.Outer.Clone100Encoding

end

end OAI
