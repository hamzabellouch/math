import Mathlib.Data.Nat.Size
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.Reductions.BinaryNameCompare

namespace OAI

namespace BinPackingCompleteness.BinaryEncoding

open BinaryFormula

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

@[simp] theorem parseFrame_encoded (bits trailing : List Bool) :
    parseFrame (frame bits ++ trailing) = some (bits, trailing) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, parseFrame, ih]

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, ih]; omega

@[simp] theorem parseName_encoded (name : Nat) (rest : List Bool) :
    parseName (nameBits name ++ rest) = some (name, rest) := by
  simp [parseName, nameBits]

@[simp] theorem nameBits_length (name : Nat) :
    (nameBits name).length = 2 * name.size + 1 := by
  simp [nameBits, Nat.size_eq_bits_len]

theorem nameBits_length_le_of_lt_pow (name width : Nat) (bound : name < 2 ^ width) :
    (nameBits name).length ≤ 2 * width + 1 := by
  rw [nameBits_length]
  have h := Nat.size_le.mpr bound
  omega

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

def parseLiteral : List Bool → Option (Literal × List Bool)
  | sign :: input => do
      let (name, rest) ← parseName input
      return (⟨name, sign⟩, rest)
  | [] => none

@[simp] theorem parseLiteral_encoded (literal : Literal) (rest : List Bool) :
    parseLiteral (literalBits literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk name sign => simp [literalBits, parseLiteral]

@[simp] theorem literalBits_length (literal : Literal) :
    (literalBits literal).length = 2 * literal.name.size + 2 := by
  simp [literalBits]

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

def parseClause (input : List Bool) : Option (Clause × List Bool) := do
  let (a, input) ← parseLiteral input
  let (b, input) ← parseLiteral input
  let (c, rest) ← parseLiteral input
  return (#v[a, b, c], rest)

theorem clause_three_entries (clause : Clause) : #v[clause[0], clause[1], clause[2]] = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded (clause : Clause) (rest : List Bool) :
    parseClause (clauseBits clause ++ rest) = some (clause, rest) := by
  simp [clauseBits, List.append_assoc, parseClause, clause_three_entries]

def clauseNameSize (clause : Clause) : Nat :=
  ((clauseNames clause).map Nat.size).sum

@[simp] theorem clauseBits_length (clause : Clause) :
    (clauseBits clause).length = 2 * clauseNameSize clause + 6 := by
  simp [clauseBits, clauseNameSize, clauseNames]
  omega

def clausesBits : List Clause → List Bool
  | [] => [false]
  | clause :: clauses => true :: (clauseBits clause ++ clausesBits clauses)

def formulaBits (formula : Formula) : List Bool := clausesBits formula.clauses

def namesBitSize (clauses : List Clause) : Nat :=
  ((clauses.flatMap clauseNames).map Nat.size).sum

@[simp] theorem namesBitSize_nil : namesBitSize [] = 0 := rfl

@[simp] theorem namesBitSize_cons (clause : Clause) (clauses : List Clause) :
    namesBitSize (clause :: clauses) = clauseNameSize clause + namesBitSize clauses := by
  simp [namesBitSize, clauseNameSize]

theorem clausesBits_length (clauses : List Clause) :
    (clausesBits clauses).length = 7 * clauses.length + 2 * namesBitSize clauses + 1 := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [clausesBits, List.length_cons, List.length_append, clauseBits_length,
        namesBitSize_cons, ih]
      omega

theorem formulaBits_length (formula : Formula) :
    (formulaBits formula).length =
      7 * formula.clauses.length + 2 * namesBitSize formula.clauses + 1 :=
  clausesBits_length formula.clauses

theorem clauses_length_lt_bits (clauses : List Clause) :
    clauses.length < (clausesBits clauses).length := by
  rw [clausesBits_length]
  omega

def ordinarySize (formula : Formula) : Nat :=
  3 * formula.clauses.length + namesBitSize formula.clauses + 1

theorem ordinarySize_le_bits (formula : Formula) :
    ordinarySize formula ≤ (formulaBits formula).length := by
  rw [formulaBits_length]
  unfold ordinarySize
  omega

theorem bits_le_three_ordinarySize (formula : Formula) :
    (formulaBits formula).length ≤ 3 * ordinarySize formula := by
  rw [formulaBits_length]
  unfold ordinarySize
  omega

def parseClauses : Nat → List Bool → Option (List Clause × List Bool)
  | 0, _ => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

@[simp] theorem parseClauses_encoded (clauses : List Clause) (rest : List Bool)
    (fuel : Nat) (enough : clauses.length < fuel) :
    parseClauses fuel (clausesBits clauses ++ rest) = some (clauses, rest) := by
  induction clauses generalizing fuel with
  | nil =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [clausesBits, parseClauses]
  | cons clause clauses ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hrest : clauses.length < fuel := by simp only [List.length_cons] at enough; omega
          simp [clausesBits, parseClauses, List.append_assoc, ih fuel hrest]

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

@[simp] theorem decodeFormula_encoded (formula : Formula) :
    decodeFormula (formulaBits formula) = some formula := by
  cases formula with
  | mk clauses =>
      have hlen := clauses_length_lt_bits clauses
      have parsed := parseClauses_encoded clauses [] ((clausesBits clauses).length + 1) (by omega)
      simp only [List.append_nil] at parsed
      simp [formulaBits, decodeFormula, parsed]

theorem formulaBits_injective {first second : Formula}
    (same : formulaBits first = formulaBits second) : first = second := by
  have parsed := congrArg decodeFormula same
  simpa only [decodeFormula_encoded, Option.some.injEq] using parsed

theorem dense_encoding_bound (formula : Formula) :
    (BinPackingGames.Foundations.Complexity.formulaBits (dense formula)).length ≤
      9 * (formulaBits formula).length * (formulaBits formula).length +
      10 * (formulaBits formula).length + 2 := by
  have h := BinaryFormula.dense_encoding_bound formula
  have hm : formula.clauses.length ≤ (formulaBits formula).length :=
    (clauses_length_lt_bits formula.clauses).le
  have hsq := Nat.mul_self_le_mul_self hm
  nlinarith

end BinPackingCompleteness.BinaryEncoding

namespace BinPackingCompleteness.BinaryParsing

open BinaryEncoding BinaryFormula

theorem frame_eq (bits : List Bool) : BinaryNameMachine.frame bits = frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [BinaryNameMachine.frame, frame, ih]

theorem canonical_cons_cons (a b : Bool) (bits : List Bool) :
    BinaryNameMachine.canonical (a :: b :: bits) = BinaryNameMachine.canonical (b :: bits) := rfl

theorem canonical_iff (bits : List Bool) :
    BinaryNameMachine.canonical bits = true ↔ (bitsValue bits).bits = bits := by
  induction bits with
  | nil => simp [BinaryNameMachine.canonical, BinaryNameMachine.finalDigit, bitsValue]
  | cons bit bits ih =>
      cases bits with
      | nil => cases bit <;> decide
      | cons next bits =>
          rw [canonical_cons_cons, ih]
          constructor
          · intro htail
            have hn : bitsValue (next :: bits) ≠ 0 := by
              intro hz
              rw [hz, Nat.zero_bits] at htail
              contradiction
            rw [bitsValue, Nat.bits_append_bit _ bit (fun h => False.elim (hn h)), htail]
          · intro hfull
            calc
              (bitsValue (next :: bits)).bits =
                  (Nat.bit bit (bitsValue (next :: bits))).div2.bits := by rw [Nat.div2_bit]
              _ = (Nat.bit bit (bitsValue (next :: bits))).bits.tail :=
                Nat.div2_bits_eq_tail _
              _ = (bit :: next :: bits).tail := congrArg List.tail hfull
              _ = next :: bits := rfl

@[simp] theorem canonical_nat_bits (name : Nat) :
    BinaryNameMachine.canonical name.bits = true := by
  apply (canonical_iff _).mpr
  rw [bitsValue_bits]

theorem parseFrame_sound (input digits rest : List Bool)
    (parsed : parseFrame input = some (digits, rest)) : input = frame digits ++ rest := by
  induction input using List.twoStepInduction generalizing digits rest with
  | nil => simp [parseFrame] at parsed
  | singleton flag =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · simp [parseFrame] at parsed
  | cons_cons flag bit input ih _ =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · cases h : parseFrame input with
        | none => simp [parseFrame, h] at parsed
        | some pair =>
            rcases pair with ⟨ds, tail⟩
            have hs := ih ds tail h
            simp [parseFrame, h] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            simp [frame, hs]

theorem parseName_sound (input : List Bool) (name : Nat) (rest : List Bool)
    (parsed : parseName input = some (name, rest)) : input = nameBits name ++ rest := by
  cases h : parseFrame input with
  | none => simp [parseName, h] at parsed
  | some pair =>
      rcases pair with ⟨digits, tail⟩
      by_cases canonical : digits = (bitsValue digits).bits
      · simp only [parseName, h, Option.bind_eq_bind, Option.bind_some] at parsed
        rw [ite_eq_left canonical] at parsed
        simp only [Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        have hs := parseFrame_sound input digits tail h
        exact hs.trans (congrArg (fun ds => frame ds ++ tail) canonical)
      · simp only [parseName, h, Option.bind_eq_bind, Option.bind_some, ite_eq_right canonical] at parsed
        cases parsed

theorem parseLiteral_sound (input : List Bool) (literal : Literal) (rest : List Bool)
    (parsed : parseLiteral input = some (literal, rest)) :
    input = literalBits literal ++ rest := by
  cases input with
  | nil => simp [parseLiteral] at parsed
  | cons sign input =>
      cases h : parseName input with
      | none => simp [parseLiteral, h] at parsed
      | some pair =>
          rcases pair with ⟨name, tail⟩
          have hs := parseName_sound input name tail h
          simp [parseLiteral, h] at parsed
          rcases parsed with ⟨rfl, rfl⟩
          simp [literalBits, hs]

theorem parseClause_sound (input : List Bool) (clause : Clause) (rest : List Bool)
    (parsed : parseClause input = some (clause, rest)) : input = clauseBits clause ++ rest := by
  cases ha : parseLiteral input with
  | none => simp [parseClause, ha] at parsed
  | some first =>
      rcases first with ⟨a, afterA⟩
      cases hb : parseLiteral afterA with
      | none => simp [parseClause, ha, hb] at parsed
      | some second =>
          rcases second with ⟨b, afterB⟩
          cases hc : parseLiteral afterB with
          | none => simp [parseClause, ha, hb, hc] at parsed
          | some third =>
              rcases third with ⟨c, afterC⟩
              have hA := parseLiteral_sound input a afterA ha
              have hB := parseLiteral_sound afterA b afterB hb
              have hC := parseLiteral_sound afterB c afterC hc
              have pairEq : (#v[a, b, c], afterC) = (clause, rest) := by
                apply Option.some.inj
                simpa only [parseClause, ha, hb, hc, Option.bind_eq_bind,
                  Option.bind_some, Option.pure_def] using parsed
              rcases Prod.mk.inj pairEq with ⟨rfl, rfl⟩
              simp [clauseBits, hA, hB, hC, List.append_assoc]

theorem parseClauses_sound (fuel : Nat) (input : List Bool)
    (clauses : List Clause) (rest : List Bool)
    (parsed : parseClauses fuel input = some (clauses, rest)) :
    input = clausesBits clauses ++ rest := by
  induction fuel generalizing input clauses rest with
  | zero => simp [parseClauses] at parsed
  | succ fuel ih =>
      cases input with
      | nil => simp [parseClauses] at parsed
      | cons flag input =>
          cases flag
          · simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            rfl
          · cases hc : parseClause input with
            | none => simp [parseClauses, hc] at parsed
            | some first =>
                rcases first with ⟨clause, afterClause⟩
                cases hs : parseClauses fuel afterClause with
                | none => simp [parseClauses, hc, hs] at parsed
                | some remaining =>
                    rcases remaining with ⟨cs, tail⟩
                    have hC := parseClause_sound input clause afterClause hc
                    have hS := ih afterClause cs tail hs
                    simp [parseClauses, hc, hs] at parsed
                    rcases parsed with ⟨rfl, rfl⟩
                    simp [clausesBits, hC, hS, List.append_assoc]

theorem decodeFormula_sound (input : List Bool) (formula : Formula)
    (parsed : decodeFormula input = some formula) : input = formulaBits formula := by
  cases h : parseClauses (input.length + 1) input with
  | none => simp [decodeFormula, h] at parsed
  | some pair =>
      rcases pair with ⟨clauses, rest⟩
      by_cases empty : rest = []
      · subst rest
        simp [decodeFormula, h] at parsed
        subst formula
        simpa only [formulaBits, List.append_nil] using
          parseClauses_sound (input.length + 1) input clauses [] h
      · simp [decodeFormula, h, empty] at parsed

theorem decodeFormula_eq_some_iff (input : List Bool) (formula : Formula) :
    decodeFormula input = some formula ↔ input = formulaBits formula :=
  ⟨decodeFormula_sound input formula, fun h => h ▸ decodeFormula_encoded formula⟩

theorem scanSpec_nameBits (name : Nat) (suffix output : List Bool) :
    BinaryNameMachine.scanSpec (nameBits name ++ suffix) output none =
      ⟨true, suffix, name.bits.reverse ++ output⟩ := by
  unfold nameBits
  rw [← frame_eq, BinaryNameMachine.scanSpec_frame]
  have h := canonical_nat_bits name
  simpa only [BinaryNameMachine.canonical] using
    congrArg (fun accepted =>
      (⟨accepted, suffix, name.bits.reverse ++ output⟩ : BinaryNameMachine.Result)) h

end BinPackingCompleteness.BinaryParsing

namespace BinPackingCompleteness.BinaryTokenMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinaryFormula BinaryEncoding

abbrev Tape := Fin 3
abbrev Alphabet (_ : Tape) := Bool
abbrev State := Unit × Option Bool

inductive Label where
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3)
  | restore
  | accept
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Label :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

@[simp] theorem afterName_zero : afterName 0 = .sign 1 := rfl
@[simp] theorem afterName_one : afterName 1 = .sign 2 := rfl
@[simp] theorem afterName_two : afterName 2 = .clause := rfl

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => ((), none)) (.goto fun _ => label)

def clauseInstruction : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (jump (.sign 0)) (jump .restore)))

def signInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
      (jump .reject))

def nameInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (.push 1 (fun _ => true)
          (.pop 0 (fun state head => (state.1, head))
            (.branch (fun state => state.2.isSome)
              (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
              (jump .reject))))
        (.push 1 (fun _ => false) (jump (afterName slot)))))

def program : Label → TM2.Stmt Alphabet Label State
  | .clause => clauseInstruction
  | .sign slot => signInstruction slot
  | .name slot => nameInstruction slot
  | .restore => loopAt 1 2 id false .restore (some .accept)
  | .accept => .halt
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := Label
  main := .clause
  σ := State
  initialState := ((), none)
  m := program

def tapes (input reversed output : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then reversed else output

def cfg (label : Option Label) (input reversed output : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input reversed output⟩

@[simp] private theorem tapes_zero (input reversed output : List Bool) :
    tapes input reversed output 0 = input := rfl

@[simp] private theorem tapes_one (input reversed output : List Bool) :
    tapes input reversed output 1 = reversed := rfl

@[simp] private theorem tapes_two (input reversed output : List Bool) :
    tapes input reversed output 2 = output := rfl

private theorem update_zero (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 0 replacement =
      tapes replacement reversed output := by
  funext k
  fin_cases k <;> simp [tapes]

private theorem update_one (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 1 replacement =
      tapes input replacement output := by
  funext k
  fin_cases k <;> simp [tapes]

theorem clauseStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (true :: input) reversed output register) =
      some (cfg (some (.sign 0)) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]
  rfl

theorem finalStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (false :: input) reversed output register) =
      some (cfg (some .restore) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]
  rfl

theorem signStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.sign slot)) (bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: reversed) output) := by
  change some (TM2.stepAux (program (.sign slot)) _ _) = _
  simp [program, signInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem nameEndStep (slot : Fin 3) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.name slot)) (false :: input) reversed output register) =
      some (cfg (some (afterName slot)) input (false :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem nameDigitStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step
      (cfg (some (.name slot)) (true :: bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: true :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem nameTrace (slot : Fin 3) (bits suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[bits.length + 1]
      (some (cfg (some (.name slot)) (frame bits ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix ((frame bits).reverse ++ reversed) output) := by
  induction bits generalizing reversed register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        frame, List.singleton_append, List.reverse_singleton] using
        nameEndStep slot suffix reversed output register
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [frame, List.cons_append, advance_some]
      rw [nameDigitStep, ih]
      simp only [List.reverse_cons, List.append_assoc,
        List.cons_append, List.nil_append]

theorem literalTrace (slot : Fin 3) (literal : Literal)
    (suffix reversed output : List Bool) (register : Option Bool) :
    (advance machine.step)^[literal.name.size + 2]
      (some (cfg (some (.sign slot)) (literalBits literal ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix
        ((literalBits literal).reverse ++ reversed) output) := by
  rw [show literal.name.size + 2 = (literal.name.bits.length + 1) + 1 by
    rw [Nat.size_eq_bits_len]]
  rw [Function.iterate_succ_apply]
  simp only [literalBits, List.cons_append, advance_some]
  rw [signStep]
  change (advance machine.step)^[literal.name.bits.length + 1]
    (some (cfg (some (.name slot)) (frame literal.name.bits ++ suffix)
      (literal.positive :: reversed) output)) = _
  rw [nameTrace]
  simp only [nameBits, List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem clauseTrace (clause : Clause) (suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[clauseNameSize clause + 6]
      (some (cfg (some (.sign 0)) (clauseBits clause ++ suffix) reversed output register)) =
      some (cfg (some .clause) suffix ((clauseBits clause).reverse ++ reversed) output) := by
  have first := literalTrace 0 clause[0]
    (literalBits clause[1] ++ literalBits clause[2] ++ suffix) reversed output register
  have second := literalTrace 1 clause[1] (literalBits clause[2] ++ suffix)
    ((literalBits clause[0]).reverse ++ reversed) output none
  have third := literalTrace 2 clause[2] suffix
    ((literalBits clause[1]).reverse ++ ((literalBits clause[0]).reverse ++ reversed)) output none
  simp only [afterName_zero, afterName_one, afterName_two, List.append_assoc]
    at first second third
  have full := joinTrace (joinTrace first second) third
  have htime : (clause[0].name.size + 2 + (clause[1].name.size + 2)) +
      (clause[2].name.size + 2) = clauseNameSize clause + 6 := by
    simp [clauseNameSize, clauseNames]
    omega
  rw [htime] at full
  simpa only [clauseBits, List.append_assoc, List.reverse_append] using full

def tokens (clauses : List Clause) : List Bool := clauses.flatMap clauseBits

@[simp] theorem tokens_nil : tokens [] = [] := rfl

@[simp] theorem tokens_cons (clause : Clause) (clauses : List Clause) :
    tokens (clause :: clauses) = clauseBits clause ++ tokens clauses := by
  simp [tokens]

@[simp] theorem tokens_length (clauses : List Clause) :
    (tokens clauses).length = 6 * clauses.length + 2 * namesBitSize clauses := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [tokens_cons, List.length_append, clauseBits_length, ih,
        List.length_cons, namesBitSize_cons]
      omega

theorem stripTrace (clauses : List Clause) (suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[7 * clauses.length + namesBitSize clauses + 1]
      (some (cfg (some .clause) (clausesBits clauses ++ suffix) reversed output register)) =
      some (cfg (some .restore) suffix ((tokens clauses).reverse ++ reversed) output) := by
  induction clauses generalizing reversed register with
  | nil =>
      simpa only [List.length_nil, Nat.mul_zero, namesBitSize_nil, Nat.add_zero,
        Nat.zero_add, Function.iterate_one, advance_some, clausesBits,
        List.singleton_append, tokens_nil, List.reverse_nil, List.nil_append] using
        finalStep suffix reversed output register
  | cons clause clauses ih =>
      have first : (advance machine.step)^[1]
          (some (cfg (some .clause)
            (true :: (clauseBits clause ++ (clausesBits clauses ++ suffix)))
            reversed output register)) =
          some (cfg (some (.sign 0))
            (clauseBits clause ++ (clausesBits clauses ++ suffix)) reversed output) := by
        simpa only [Function.iterate_one, advance_some] using
          clauseStep (clauseBits clause ++ (clausesBits clauses ++ suffix)) reversed output register
      have second := clauseTrace clause (clausesBits clauses ++ suffix) reversed output none
      have third := ih ((clauseBits clause).reverse ++ reversed) none
      have full := joinTrace (joinTrace first second) third
      have htime : (1 + (clauseNameSize clause + 6)) +
          (7 * clauses.length + namesBitSize clauses + 1) =
          7 * (clause :: clauses).length + namesBitSize (clause :: clauses) + 1 := by
        simp only [List.length_cons, namesBitSize_cons]
        omega
      rw [htime] at full
      simpa only [clausesBits, List.cons_append, List.append_assoc,
        tokens_cons, List.reverse_append] using full

theorem restoreTrace (input unread output : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .restore) unread input.reverse output register)) =
      some (cfg (some .accept) unread [] (input ++ output)) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 2 (by decide)
    id false .restore (some .accept) program rfl
    (tapes unread input.reverse output) () register
  have ht : tapesAt 1 2 (tapes unread input.reverse output) [] (input ++ output) =
      tapes unread [] (input ++ output) := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 2 program)^[input.length + 1]
    (some (cfg (some .restore) unread input.reverse output register)) = _
  simpa only [tapes_one, tapes_two, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, ht, nextAt, advance, cfg] using! h

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .clause) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] [] output := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem acceptTrace (formula : Formula) :
    (advance machine.step)^[13 * formula.clauses.length +
        3 * namesBitSize formula.clauses + 2]
      (some (initList machine (formulaBits formula))) =
      some (cfg (some .accept) [] [] (tokens formula.clauses)) := by
  have first := stripTrace formula.clauses [] [] [] none
  simp only [List.append_nil] at first
  have second := restoreTrace (tokens formula.clauses) [] [] none
  simp only [List.append_nil] at second
  have full := joinTrace first second
  have htime : (7 * formula.clauses.length + namesBitSize formula.clauses + 1) +
      ((tokens formula.clauses).length + 1) =
      13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 2 := by
    rw [tokens_length]
    omega
  rw [htime] at full
  simpa only [initList_eq, BinaryEncoding.formulaBits] using full

theorem haltStep (output : List Bool) :
    machine.step (cfg (some .accept) [] [] output) = some (cfg none [] [] output) := by
  change some (TM2.stepAux (program .accept) _ _) = _
  rfl

theorem tokenTrace (formula : Formula) :
    (advance machine.step)^[13 * formula.clauses.length +
        3 * namesBitSize formula.clauses + 3]
      (some (initList machine (formulaBits formula))) =
      some (haltList machine (tokens formula.clauses)) := by
  rw [show 13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3 =
    (13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 2) + 1 by omega,
    Function.iterate_succ_apply', acceptTrace, advance_some, haltStep, haltList_eq]

theorem tokenSteps_le (formula : Formula) :
    13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3 ≤
      3 * (formulaBits formula).length + 3 := by
  rw [BinaryEncoding.formulaBits_length]
  omega

def outputsInTime (formula : Formula) :
    TM2OutputsInTime machine (formulaBits formula) (some (tokens formula.clauses))
      (3 * (formulaBits formula).length + 3) where
  steps := 13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3
  evals_in_steps := tokenTrace formula
  steps_le_m := tokenSteps_le formula

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits (id : List Bool → List Bool)
      (fun formula => tokens formula.clauses) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
  outputsFun formula := by
    change TM2OutputsInTime machine ((formulaBits formula).map id)
      (some ((tokens formula.clauses).map id))
      ((Polynomial.C 3 * Polynomial.X + Polynomial.C 3 : Polynomial Nat).eval
        (formulaBits formula).length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using outputsInTime formula

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end BinPackingCompleteness.BinaryTokenMachine

end OAI
