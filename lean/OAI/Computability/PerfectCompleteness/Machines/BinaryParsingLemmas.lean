import OAI.Computability.PerfectCompleteness.Machines.BinaryFormulaLemmas
import OAI.Computability.PerfectCompleteness.Machines.BinaryNameMachine
import OAI.Computability.PerfectCompleteness.Machines.BinaryOccurrenceRename
import OAI.Computability.PerfectCompleteness.Model

namespace OAI


namespace PerfectCompleteness.BinaryParsing

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

end PerfectCompleteness.BinaryParsing



namespace PerfectCompleteness.BinaryLanguage

open UniqueGamesTheorem.Foundations

def rejectBinary : BinaryFormula.Formula where
  clauses := [#v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩],
    #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]]

theorem rejectBinary_unsatisfiable : ¬rejectBinary.Satisfiable := by
  rintro ⟨assignment, satisfied⟩
  have positive := satisfied #v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩]
    (by simp [rejectBinary])
  have negative := satisfied #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]
    (by simp [rejectBinary])
  cases h : assignment 0 <;>
    simp [BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, h] at positive negative

def rejectFormula : Target.Formula := BinaryOccurrenceRename.renamed rejectBinary

theorem reject_unsatisfiable : ¬rejectFormula.Satisfiable := by
  simpa only [rejectFormula, BinaryOccurrenceRename.renamed_satisfiable_iff] using
    rejectBinary_unsatisfiable

def totalParsed (input : List Bool) : BinaryFormula.Formula :=
  (BinaryEncoding.decodeFormula input).getD rejectBinary

def totalRename (input : List Bool) : Target.Formula :=
  BinaryOccurrenceRename.renamed (totalParsed input)

theorem totalParsed_satisfiable_iff (input : List Bool) :
    (totalParsed input).Satisfiable ↔ language input := by
  cases parsed : BinaryEncoding.decodeFormula input with
  | none => simp [totalParsed, parsed, rejectBinary_unsatisfiable, language]
  | some formula => simp [totalParsed, parsed, language]

theorem totalRename_satisfiable_iff (input : List Bool) :
    (totalRename input).Satisfiable ↔ language input := by
  exact (BinaryOccurrenceRename.renamed_satisfiable_iff (totalParsed input)).trans
    (totalParsed_satisfiable_iff input)

theorem totalRename_encoded (formula : BinaryFormula.Formula) :
    totalRename (BinaryEncoding.formulaBits formula) = BinaryOccurrenceRename.renamed formula := by
  simp [totalRename, totalParsed]

theorem language_encoded (formula : BinaryFormula.Formula) :
    language (BinaryEncoding.formulaBits formula) ↔ formula.Satisfiable := by
  simp [language]

theorem reject_bits_length : (Complexity.formulaBits rejectFormula).length = 25 := by decide

theorem totalRename_output_length (input : List Bool) :
    (Complexity.formulaBits (totalRename input)).length ≤
      9 * input.length * input.length + 10 * input.length + 25 := by
  cases parsed : BinaryEncoding.decodeFormula input with
  | none =>
      have output : totalRename input = rejectFormula := by simp [totalRename, totalParsed, parsed, rejectFormula]
      rw [output, reject_bits_length]
      omega
  | some formula =>
      have correct := BinaryParsing.decodeFormula_sound input formula parsed
      have bound := BinaryOccurrenceRename.renamed_encoding_bound_bits formula
      simp only [totalRename, totalParsed, parsed, Option.getD_some]
      rw [correct]
      omega

end PerfectCompleteness.BinaryLanguage

end OAI
