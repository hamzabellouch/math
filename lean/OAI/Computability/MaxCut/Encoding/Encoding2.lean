import Mathlib
import OAI.Computability.MaxCut.PCP.Folding

namespace OAI

/-! An occurrence-preserving E3LIN table codec. The word stream contains its
declared variable count and equation count, followed by four words per equation.
Parsing checks all three indices, the Boolean right-hand side, the exact count,
absence of trailing words, and nonemptiness. Length theorems below concern the
actual serialized output; they make no running-time claim. -/

namespace MaxCutGames.Reduction.SourceEncoding

open MaxCutGames.Foundations.Complexity

structure Input where
  «variables» : Nat
  equations : List (CloneGap.Equation (Fin «variables»))
  nonempty : equations ≠ []

abbrev Table := Input

def equationWords {n : Nat} (e : CloneGap.Equation (Fin n)) : List Nat :=
  [e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0]

def inputWords (input : Input) : List Nat :=
  [input.«variables», input.equations.length] ++ input.equations.flatMap equationWords

def inputBits (input : Input) : List Bool := encodeWords (inputWords input)

def parseEquation («variables» : Nat) :
    List Nat → Option (CloneGap.Equation (Fin «variables») × List Nat)
  | first :: second :: third :: rhs :: rest =>
      if hfirst : first < «variables» then
        if hsecond : second < «variables» then
          if hthird : third < «variables» then
            if rhs = 0 then
              some (⟨⟨first, hfirst⟩, ⟨second, hsecond⟩, ⟨third, hthird⟩, false⟩, rest)
            else if rhs = 1 then
              some (⟨⟨first, hfirst⟩, ⟨second, hsecond⟩, ⟨third, hthird⟩, true⟩, rest)
            else none
          else none
        else none
      else none
  | _ => none

@[simp] theorem parseEquation_encoded {n : Nat} (e : CloneGap.Equation (Fin n))
    (rest : List Nat) :
    parseEquation n (equationWords e ++ rest) = some (e, rest) := by
  cases e with
  | mk first second third rhs =>
      cases rhs <;> simp [equationWords, parseEquation, first.isLt, second.isLt, third.isLt]

def parseEquations («variables» : Nat) :
    Nat → List Nat → Option (List (CloneGap.Equation (Fin «variables»)) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (equation, words) ← parseEquation «variables» words
      let (equations, words) ← parseEquations «variables» count words
      return (equation :: equations, words)

/-- Parsing preserves the entire ordered list, including all equal entries. -/
@[simp] theorem parseEquations_encoded {n : Nat}
    (equations : List (CloneGap.Equation (Fin n))) (rest : List Nat) :
    parseEquations n equations.length (equations.flatMap equationWords ++ rest) =
      some (equations, rest) := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp [List.append_assoc, parseEquations, parseEquation_encoded, ih]

def decodeInputWords : List Nat → Option Input
  | «variables» :: count :: words => do
      let (equations, trailing) ← parseEquations «variables» count words
      if trailing = [] then
        if nonempty : 0 < equations.length then
          some ⟨«variables», equations, List.length_pos_iff.mp nonempty⟩
        else none
      else none
  | _ => none

@[simp] theorem decodeInputWords_encoded (input : Input) :
    decodeInputWords (inputWords input) = some input := by
  cases input with
  | mk «variables» equations nonempty =>
      have parsed := parseEquations_encoded equations []
      have positive := List.length_pos_iff.mpr nonempty
      simp only [List.append_nil] at parsed
      simp [decodeInputWords, inputWords, parsed, positive]

def decodeInputBits (bits : List Bool) : Option Input :=
  decodeWords bits >>= decodeInputWords

@[simp] theorem decodeInputBits_encoded (input : Input) :
    decodeInputBits (inputBits input) = some input := by
  simp [decodeInputBits, inputBits]

theorem inputWords_injective {first second : Input}
    (same : inputWords first = inputWords second) : first = second := by
  have parsed := congrArg decodeInputWords same
  simpa only [decodeInputWords_encoded, Option.some.injEq] using parsed

theorem inputBits_injective {first second : Input}
    (same : inputBits first = inputBits second) : first = second := by
  have parsed := congrArg decodeInputBits same
  simpa only [decodeInputBits_encoded, Option.some.injEq] using parsed

@[simp] theorem equationWords_length {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (equationWords e).length = 4 := by simp [equationWords]

theorem equationsWords_length {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (equations.flatMap equationWords).length = 4 * equations.length := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp only [List.flatMap_cons, List.length_append, equationWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem inputWords_length (input : Input) :
    (inputWords input).length = 2 + 4 * input.equations.length := by
  simp only [inputWords, List.length_append, List.length_cons, List.length_nil,
    equationsWords_length]

theorem equationBits_length_le {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (encodeWords (equationWords e)).length ≤ 3 * n + 2 := by
  have hfirst := e.first.isLt
  have hsecond := e.second.isLt
  have hthird := e.third.isLt
  cases hrhs : e.rhs <;> simp [equationWords, hrhs] <;> omega

theorem equationsBits_length_le {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (encodeWords (equations.flatMap equationWords)).length ≤
      equations.length * (3 * n + 2) := by
  induction equations with
  | nil => simp [encodeWords]
  | cons e equations ih =>
      have he := equationBits_length_le e
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem inputBits_length (input : Input) :
    (inputBits input).length = input.«variables» + input.equations.length + 2 +
      (encodeWords (input.equations.flatMap equationWords)).length := by
  simp only [inputBits, inputWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem inputBits_length_le (input : Input) :
    (inputBits input).length ≤ input.«variables» + input.equations.length + 2 +
      input.equations.length * (3 * input.«variables» + 2) := by
  rw [inputBits_length]
  exact Nat.add_le_add_left (equationsBits_length_le input.equations) _

theorem inputBits_length_ge_variables (input : Input) :
    input.«variables» ≤ (inputBits input).length := by rw [inputBits_length]; omega

theorem inputBits_length_ge_equations (input : Input) :
    input.equations.length ≤ (inputBits input).length := by rw [inputBits_length]; omega

end MaxCutGames.Reduction.SourceEncoding

end OAI
