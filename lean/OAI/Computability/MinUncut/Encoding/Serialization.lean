import Mathlib
import OAI.Computability.MinUncut.PCP.Folding
import OAI.Computability.MinUncut.Games.Target

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

def decodeWordsAux : List Bool → Nat → Option (List Nat)
  | [], 0 => some []
  | [], _ + 1 => none
  | true :: bs, n => decodeWordsAux bs (n + 1)
  | false :: bs, n => (decodeWordsAux bs 0).map (n :: ·)

def decodeWords (bs : List Bool) : Option (List Nat) := decodeWordsAux bs 0

theorem decodeWordsAux_word (n k : Nat) (bs : List Bool) :
    decodeWordsAux (encodeWord n ++ bs) k =
      (decodeWordsAux bs 0).map ((k + n) :: ·) := by
  induction n generalizing k with
  | zero => simp [encodeWord, decodeWordsAux]
  | succ n ih =>
      simp only [encodeWord, List.replicate_succ, List.cons_append, List.append_assoc,
        decodeWordsAux]
      simpa [encodeWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

@[simp] theorem decodeWords_encodeWords (ns : List Nat) :
    decodeWords (encodeWords ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [decodeWords, encodeWords, decodeWordsAux_word, Nat.zero_add]
      simpa [decodeWords] using congrArg (Option.map (n :: ·)) ih

theorem encodeWords_injective {xs ys : List Nat} (h : encodeWords xs = encodeWords ys) :
    xs = ys := by
  have decoded := congrArg decodeWords h
  simpa only [decodeWords_encodeWords, Option.some.injEq] using decoded

@[simp] theorem encodeWord_length (n : Nat) : (encodeWord n).length = n + 1 := by
  simp [encodeWord]

@[simp] theorem encodeWords_append (xs ys : List Nat) :
    encodeWords (xs ++ ys) = encodeWords xs ++ encodeWords ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih, List.append_assoc]

@[simp] theorem encodeWords_length (ns : List Nat) :
    (encodeWords ns).length = ns.sum + ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [encodeWords, ih]; omega

theorem encodeWords_length_le (ns : List Nat) (bound : Nat)
    (bounded : ∀ n ∈ ns, n ≤ bound) :
    (encodeWords ns).length ≤ ns.length * (bound + 1) := by
  induction ns with
  | nil => simp [encodeWords]
  | cons n ns ih =>
      have hn := bounded n (by simp)
      have hns := ih (fun x hx => bounded x (by simp [hx]))
      simp only [encodeWords, List.length_append, encodeWord_length, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

open Target

def literalWords {n : Nat} (literal : Literal n) : List Nat :=
  [literal.variableIndex.val, if literal.positive then 1 else 0]

def clauseWords {n : Nat} (clause : Clause n) : List Nat :=
  literalWords clause[0] ++ literalWords clause[1] ++ literalWords clause[2]

def formulaWords (formula : Formula) : List Nat :=
  [formula.«variables», formula.clauses.length] ++ formula.clauses.flatMap clauseWords

def formulaBits (formula : Formula) : List Bool := encodeWords (formulaWords formula)

@[simp] theorem literalWords_length {n : Nat} (literal : Literal n) :
    (literalWords literal).length = 2 := by simp [literalWords]

@[simp] theorem clauseWords_length {n : Nat} (clause : Clause n) :
    (clauseWords clause).length = 6 := by simp [clauseWords]

theorem clausesWords_length {n : Nat} (clauses : List (Clause n)) :
    (clauses.flatMap clauseWords).length = 6 * clauses.length := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [List.flatMap_cons, List.length_append, clauseWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem formulaWords_length (formula : Formula) :
    (formulaWords formula).length = 2 + 6 * formula.clauses.length := by
  simp only [formulaWords, List.length_append, List.length_cons, List.length_nil,
    clausesWords_length]

theorem literalBits_length_le {n : Nat} (literal : Literal n) :
    (encodeWords (literalWords literal)).length ≤ n + 2 := by
  have hindex := literal.variableIndex.isLt
  cases hp : literal.positive <;> simp [literalWords, hp]

theorem clauseBits_length_le {n : Nat} (clause : Clause n) :
    (encodeWords (clauseWords clause)).length ≤ 3 * (n + 2) := by
  have h0 := literalBits_length_le clause[0]
  have h1 := literalBits_length_le clause[1]
  have h2 := literalBits_length_le clause[2]
  simp only [clauseWords, encodeWords_append, List.length_append]
  omega

theorem clausesBits_length_le {n : Nat} (clauses : List (Clause n)) :
    (encodeWords (clauses.flatMap clauseWords)).length ≤ clauses.length * (3 * (n + 2)) := by
  induction clauses with
  | nil => simp [encodeWords]
  | cons clause clauses ih =>
      have hc := clauseBits_length_le clause
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem formulaBits_length_le (formula : Formula) :
    (formulaBits formula).length ≤
      formula.«variables» + formula.clauses.length + 2 +
        formula.clauses.length * (3 * (formula.«variables» + 2)) := by
  have h := clausesBits_length_le formula.clauses
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end MinUncutGames.Foundations.Complexity

end
section
namespace MinUncutGames.Reduction.SourceEncoding

open MinUncutGames.Foundations.Complexity

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

end MinUncutGames.Reduction.SourceEncoding

end

end OAI
