import OAI.Computability.UniqueGames.Machines.MachineBinaryFormulaLemmas
import OAI.Computability.UniqueGames.Machines.MachineBinaryNameSearch
import OAI.Computability.UniqueGames.Machines.MachineBinaryParsingLemmas
import OAI.Computability.UniqueGames.Machines.MachineBinaryTokenMachine

namespace OAI

section

/-!
The word-level correspondence used by the ordinary-binary renaming machine.
Literal occurrences stay in clause order, and equality is tested on canonical
binary payloads. The output body consists of the first occurrence index and
the sign of every literal, in the inherited dense formula codec.
-/

namespace UniqueGamesTheorem.BinaryRenameWords

open BinaryFormula UniqueGamesTheorem.Foundations

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

/-- The marker-removal machine's actual output is the search machine's stream. -/
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

/-- The output contains every literal occurrence, including repetitions. -/
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

/-- Exact ordinary-binary-machine target, including its two count headers. -/
theorem encoded_renamed (F : Formula) :
    Complexity.formulaBits (BinaryOccurrenceRename.renamed F) =
      Complexity.encodeWord (3 * F.clauses.length) ++
        Complexity.encodeWord F.clauses.length ++ body F := by
  simp only [Complexity.formulaBits, Complexity.formulaWords, Complexity.encodeWords_append,
    Complexity.encodeWords, List.append_nil,
    BinaryOccurrenceRename.renamed_variable_count,
    BinaryOccurrenceRename.renamed_clause_count, encoded_body, List.append_assoc]

end UniqueGamesTheorem.BinaryRenameWords

end

end OAI
