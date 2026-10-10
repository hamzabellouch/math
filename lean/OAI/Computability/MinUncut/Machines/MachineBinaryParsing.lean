import Mathlib
import OAI.Computability.MinUncut.Machines.MachineBinaryOccurrenceRename
import OAI.Computability.MinUncut.Machines.MachineBinaryNameMachine

namespace OAI

namespace MinUncutGames.BinaryParsing

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

end MinUncutGames.BinaryParsing

namespace MinUncutGames.BinaryTokenMachine

open Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer
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
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]; rfl

theorem finalStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (false :: input) reversed output register) =
      some (cfg (some .restore) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]; rfl

theorem signStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.sign slot)) (bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: reversed) output) := by
  change some (TM2.stepAux (program (.sign slot)) _ _) = _
  simp [program, signInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]; rfl

theorem nameEndStep (slot : Fin 3) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.name slot)) (false :: input) reversed output register) =
      some (cfg (some (afterName slot)) input (false :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]; rfl

theorem nameDigitStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step
      (cfg (some (.name slot)) (true :: bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: true :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]; rfl

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

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
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

end MinUncutGames.BinaryTokenMachine

namespace MinUncutGames.BinaryRenameWords

open BinaryFormula MinUncutGames.Foundations

def clauseLiterals (c : Clause) : List Literal := [(c)[0], (c)[1], (c)[2]]

def literals (clauses : List Clause) : List Literal := clauses.flatMap clauseLiterals

def token (literal : Literal) : BinaryNameSearch.Token :=
  (literal.positive, literal.name.bits)

def tokens (clauses : List Clause) : List BinaryNameSearch.Token :=
  (literals clauses).map token

@[simp] theorem literals_nil : literals [] = [] := rfl

@[simp] theorem literals_cons (c : Clause) (cs : List Clause) :
    literals (c :: cs) = (c)[0] :: (c)[1] :: (c)[2] :: literals cs := rfl

@[simp] theorem literals_length (cs : List Clause) :
    (literals cs).length = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [literals_cons, List.length_cons, ih]; omega

@[simp] theorem tokens_length (cs : List Clause) :
    (tokens cs).length = 3 * cs.length := by simp [tokens]

theorem literals_names (F : Formula) :
    (literals F.clauses).map Literal.name = sourceNames F := by
  simp only [literals, sourceNames, List.map_flatMap]
  rfl

theorem tokens_payloads (F : Formula) :
    BinaryNameSearch.payloads (tokens F.clauses) = (sourceNames F).map Nat.bits := by
  rw [← literals_names]
  simp only [BinaryNameSearch.payloads, tokens, List.map_map, token, Function.comp_def]

theorem token_bits (literal : Literal) :
    BinaryNameSearch.tokenBits (token literal) = BinaryEncoding.literalBits literal := by
  simp only [BinaryNameSearch.tokenBits, token, BinaryEncoding.literalBits,
    BinaryEncoding.nameBits, BinaryParsing.frame_eq]

theorem tokens_stream (cs : List Clause) :
    BinaryNameSearch.stream (tokens cs) = BinaryTokenMachine.tokens cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [tokens, literals_cons, List.map_cons, BinaryNameSearch.stream_cons,
        token_bits, BinaryTokenMachine.tokens_cons, BinaryEncoding.clauseBits]
      simpa only [tokens, List.append_assoc] using
        congrArg (fun tail => BinaryEncoding.literalBits (c)[0] ++
          BinaryEncoding.literalBits (c)[1] ++ BinaryEncoding.literalBits (c)[2] ++ tail) ih

theorem tokens_canonical (cs : List Clause) :
    ∀ t ∈ tokens cs, BinaryNameMachine.canonical t.2 = true := by
  intro t mem
  obtain ⟨literal, _, rfl⟩ := List.mem_map.mp mem
  exact BinaryParsing.canonical_nat_bits literal.name

theorem payload_index (F : Formula) (name : Nat) :
    (BinaryNameSearch.payloads (tokens F.clauses)).idxOf name.bits =
      (sourceNames F).idxOf name := by
  rw [tokens_payloads, BinaryOccurrenceRename.idxOf_binary_payloads]

theorem token_payload_mem (cs : List Clause) (literal : Literal)
    (mem : literal ∈ literals cs) :
    literal.name.bits ∈ BinaryNameSearch.payloads (tokens cs) := by
  apply List.mem_map.mpr
  refine ⟨token literal, ?_, rfl⟩
  exact List.mem_map.mpr ⟨literal, mem, rfl⟩

theorem payloadSize_tokens (cs : List Clause) :
    BinaryNameSearch.payloadSize (tokens cs) = BinaryEncoding.namesBitSize cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [tokens, literals_cons, List.map_cons,
        BinaryNameSearch.payloadSize_cons, token, Nat.size_eq_bits_len,
        BinaryEncoding.namesBitSize_cons] at *
      simpa only [BinaryEncoding.clauseNameSize, BinaryFormula.clauseNames,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero, Nat.add_assoc] using congrArg
        (fun tail => (c)[0].name.size + ((c)[1].name.size + ((c)[2].name.size + tail))) ih

def outputLiteral (names : List Nat) (literal : Literal) : List Bool :=
  Complexity.encodeWord (names.idxOf literal.name) ++
    Complexity.encodeWord (if literal.positive then 1 else 0)

def body (F : Formula) : List Bool :=
  (literals F.clauses).flatMap (outputLiteral (sourceNames F))

theorem encoded_clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Complexity.encodeWords (Complexity.clauseWords (BinaryOccurrenceRename.clause F c mem)) =
      (clauseLiterals c).flatMap (outputLiteral (sourceNames F)) := by
  simp [Complexity.clauseWords, Complexity.literalWords, Complexity.encodeWords,
    BinaryOccurrenceRename.clause, BinaryOccurrenceRename.literal,
    BinaryOccurrenceRename.nameIndex, clauseLiterals, outputLiteral, List.append_assoc]
  rfl

private theorem encodeWords_flatMap {α : Type} (xs : List α) (f : α → List Nat) :
    Complexity.encodeWords (xs.flatMap f) =
      xs.flatMap (fun x => Complexity.encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, Complexity.encodeWords_append, ih]

theorem encoded_body (F : Formula) :
    Complexity.encodeWords ((BinaryOccurrenceRename.renamed F).clauses.flatMap
      Complexity.clauseWords) = body F := by
  rw [encodeWords_flatMap]
  change (F.clauses.attach.map (fun c => BinaryOccurrenceRename.clause F c.val c.property)).flatMap
    (fun c => Complexity.encodeWords (Complexity.clauseWords c)) = body F
  rw [List.flatMap_map]
  simp only [encoded_clause]
  have h := congrArg (fun cs : List Clause =>
    cs.flatMap (fun c => (clauseLiterals c).flatMap (outputLiteral (sourceNames F))))
    (List.attach_map_subtype_val F.clauses)
  simpa only [List.flatMap_map, body, literals, List.flatMap_assoc] using h

theorem encoded_renamed (F : Formula) :
    Complexity.formulaBits (BinaryOccurrenceRename.renamed F) =
      Complexity.encodeWord (3 * F.clauses.length) ++
        Complexity.encodeWord F.clauses.length ++ body F := by
  simp only [Complexity.formulaBits, Complexity.formulaWords, Complexity.encodeWords_append,
    Complexity.encodeWords, List.append_nil,
    BinaryOccurrenceRename.renamed_variable_count,
    BinaryOccurrenceRename.renamed_clause_count, encoded_body, List.append_assoc]

end MinUncutGames.BinaryRenameWords

namespace MinUncutGames.BinaryHeaderMachine

open Turing
open MinUncutGames.Foundations.Complexity
open MachineComposition
open MinUncutGames.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

def delimiter (destination : K) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

def tapes (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base variableTape variableCounter)
    clauses clauseCounter) destination output

@[simp] theorem tapes_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output variableTape =
      variableCounter := by
  simp [tapes, vc, vd]

@[simp] theorem tapes_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output clauses =
      clauseCounter := by
  simp [tapes, cd]

@[simp] theorem tapes_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output destination =
      output := by
  simp [tapes]

theorem tapes_other (variableTape clauses destination k : K)
    (kv : k ≠ variableTape) (kc : k ≠ clauses) (kd : k ≠ destination)
    (base : K → List Bool) (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output k = base k := by
  simp [tapes, kv, kc, kd]

private theorem update_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      variableTape replacement = tapes variableTape clauses destination base replacement clauseCounter output := by
  funext k
  by_cases hv : k = variableTape
  · subst k
    simp [tapes, vc, vd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hv]
    · by_cases hc : k = clauses
      · subst k
        simp [tapes, hv, hd]
      · simp [tapes, hv, hc, hd]

private theorem update_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      clauses replacement = tapes variableTape clauses destination base variableCounter replacement output := by
  funext k
  by_cases hc : k = clauses
  · subst k
    simp [tapes, cd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hc]
    · simp [tapes, hc, hd]

private theorem update_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      destination replacement = tapes variableTape clauses destination base variableCounter clauseCounter replacement := by
  simp [tapes]

variable (variableTape clauses destination : K)
variable (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
variable (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atClauseStart : program clauseStart = delimiter destination clauseLoop)
variable (atClauseLoop : program clauseLoop =
  loopAt clauses destination id false clauseLoop (some variableStart))
variable (atVariableStart : program variableStart = delimiter destination variableLoop)
variable (atVariableLoop : program variableLoop =
  loopAt variableTape destination id false variableLoop exit)
variable (base : K → List Bool) (ambient : A)

include atClauseStart in
theorem clauseDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some clauseLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program clauseStart) _ _) = _
  rw [atClauseStart]
  simp [delimiter, TM2.stepAux, update_destination]

include atVariableStart in
theorem variableDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some variableStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some variableLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program variableStart) _ _) = _
  rw [atVariableStart]
  simp [delimiter, TM2.stepAux, update_destination]

include cd atClauseLoop in
theorem clauseCounterTrace (m : Nat) (variableCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[m + 1]
      (some ⟨some clauseLoop, (ambient, register),
        tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) =
      some ⟨some variableStart, (ambient, none),
        tapes variableTape clauses destination base variableCounter [] (List.replicate m true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) clauses destination cd id false
    clauseLoop (some variableStart) program atClauseLoop
    (tapes variableTape clauses destination base variableCounter (List.replicate m true) output)
    ambient register
  change (nextAt destination program)^[m + 1]
    (some ⟨some clauseLoop, (ambient, register),
      tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) = _
  simpa only [tapes_clauses variableTape clauses destination cd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_clauses variableTape clauses destination cd, update_destination,
    nextAt, advance] using h

include vc vd atVariableLoop in
theorem variableCounterTrace (n : Nat) (clauseCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[n + 1]
      (some ⟨some variableLoop, (ambient, register),
        tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] clauseCounter (List.replicate n true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) variableTape destination vd id false
    variableLoop exit program atVariableLoop
    (tapes variableTape clauses destination base (List.replicate n true) clauseCounter output)
    ambient register
  change (nextAt destination program)^[n + 1]
    (some ⟨some variableLoop, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) = _
  simpa only [tapes_variables variableTape clauses destination vc vd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_variables variableTape clauses destination vc vd, update_destination,
    nextAt, advance] using h

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

include vc vd cd atClauseStart atClauseLoop atVariableStart atVariableLoop

theorem headerTrace (n m : Nat) (body : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[n + m + 4]
      (some ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base
          (List.replicate n true) (List.replicate m true) body⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] [] (encodeWord n ++ encodeWord m ++ body)⟩ := by
  have first := clauseDelimiterStep variableTape clauses destination clauseStart clauseLoop program
    atClauseStart base ambient (List.replicate n true) (List.replicate m true) body register
  change (advance (TM2.step program))^[1]
    (some ⟨some clauseStart, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) (List.replicate m true) body⟩) = _ at first
  have second := clauseCounterTrace variableTape clauses destination cd clauseLoop variableStart program
    atClauseLoop base ambient m (List.replicate n true) (false :: body) none
  have third := variableDelimiterStep variableTape clauses destination variableStart variableLoop program
    atVariableStart base ambient (List.replicate n true) []
    (List.replicate m true ++ false :: body) none
  change (advance (TM2.step program))^[1]
    (some ⟨some variableStart, (ambient, none),
      tapes variableTape clauses destination base (List.replicate n true) []
        (List.replicate m true ++ false :: body)⟩) = _ at third
  have fourth := variableCounterTrace variableTape clauses destination vc vd variableLoop exit program
    atVariableLoop base ambient n [] (false :: (List.replicate m true ++ false :: body)) none
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  have htime : ((1 + (m + 1)) + 1) + (n + 1) = n + m + 4 := by omega
  rw [htime] at full
  simpa only [encodeWord, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append] using full

def headerInTime (n m : Nat) (body : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base (List.replicate n true) (List.replicate m true) body⟩
      (some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] [] (encodeWord n ++ encodeWord m ++ body)⟩)
      (n + m + 4) where
  steps := n + m + 4
  evals_in_steps := headerTrace variableTape clauses destination vc vd cd
    clauseStart clauseLoop variableStart variableLoop exit program
    atClauseStart atClauseLoop atVariableStart atVariableLoop base ambient n m body register
  steps_le_m := Nat.le_refl _

end Placement

abbrev ConcreteTape := Fin 3
abbrev ConcreteLabel := Fin 4

def concreteProgram (label : ConcreteLabel) :
    TM2.Stmt (Alphabet (K := ConcreteTape)) ConcreteLabel (State Unit) :=
  if label = 0 then delimiter 2 1
  else if label = 1 then loopAt 1 2 id false 1 (some 2)
  else if label = 2 then delimiter 2 3
  else loopAt 0 2 id false 3 none

abbrev machine : FinTM2 where
  K := ConcreteTape
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := ConcreteLabel
  main := 0
  σ := State Unit
  initialState := ((), none)
  m := concreteProgram

def start (n m : Nat) (body : List Bool) : machine.Cfg :=
  ⟨some 0, ((), none),
    tapes 0 1 2 (fun _ : ConcreteTape => []) (List.replicate n true) (List.replicate m true) body⟩

theorem haltList_eq (body : List Bool) :
    haltList machine body =
      ⟨none, ((), none), tapes 0 1 2 (fun _ : ConcreteTape => []) [] [] body⟩ := by
  unfold haltList
  congr 1
  funext k
  fin_cases k <;> simp [machine, tapes]

def machineInTime (n m : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime machine.step (start n m body)
      (some (haltList machine (encodeWord n ++ encodeWord m ++ body))) (n + m + 4) := by
  rw [haltList_eq]
  exact headerInTime (0 : ConcreteTape) 1 2 (by decide) (by decide) (by decide)
    (0 : ConcreteLabel) 1 2 3 none concreteProgram
    (by simp [concreteProgram]) (by simp [concreteProgram])
    (by simp [concreteProgram]) (by simp [concreteProgram])
    (fun _ => []) () n m body none

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end MinUncutGames.BinaryHeaderMachine

end OAI
