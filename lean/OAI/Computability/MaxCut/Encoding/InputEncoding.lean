import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

namespace MaxCutGames.BinaryFormula

/-- An ordinary conjunction of three-slot clauses with sparse variable names.
Repeated names and repeated literals are permitted in every clause. -/

def clauseNames (clause : Clause) : List Nat :=
  [clause[0].name, clause[1].name, clause[2].name]

end MaxCutGames.BinaryFormula

namespace MaxCutGames.BinaryEncoding

open BinaryFormula

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

/-- Prefix-free framing on the two-symbol input alphabet. -/

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

/-- Equality with the canonical digits rejects alternate padded encodings. -/

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

@[simp] theorem parseLiteral_encoded (literal : Literal) (rest : List Bool) :
    parseLiteral (literalBits literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk name sign => simp [literalBits, parseLiteral]

@[simp] theorem literalBits_length (literal : Literal) :
    (literalBits literal).length = 2 * literal.name.size + 2 := by
  simp [literalBits]

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

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

/-- Binary digits, one sign per literal, and one terminal bit form a natural
reference size. The concrete framing adds only a fixed multiplicative factor. -/
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

/-- Fuel bounds the number of clause iterations, not the size of any name. -/

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

@[simp] theorem decodeFormula_encoded (formula : Formula) :
    decodeFormula (formulaBits formula) = some formula := by
  cases formula with
  | mk clauses =>
      have hlen := clauses_length_lt_bits clauses
      have parsed := parseClauses_encoded clauses [] ((clausesBits clauses).length + 1) (by omega)
      simp only [List.append_nil] at parsed
      simp [formulaBits, decodeFormula, parsed]

/-- This preserves every literal and clause occurrence, including duplicates. -/
theorem formulaBits_injective {first second : Formula}
    (same : formulaBits first = formulaBits second) : first = second := by
  have parsed := congrArg decodeFormula same
  simpa only [decodeFormula_encoded, Option.some.injEq] using parsed

end MaxCutGames.BinaryEncoding

/- The ordinary binary 3SAT language, including rejection of malformed words,
is exactly `MaxCutGames.BinaryLanguage.language`. -/

/- A finite simple unweighted graph with its full Boolean adjacency table.
Symmetry and the zero diagonal forbid directed edges, loops and repetitions.
No real/rational edge weights occur. -/

/- Each unordered distinct edge crossing the cut is counted exactly once. -/

/- An actual finite maximum, not a supremum over a relaxed cut domain. -/

/- A full binary output encoding: canonical delimited binary size, canonical
delimited binary Q, followed by the complete n-by-n Boolean adjacency table,
in lexicographic order. Thus neither Q nor adjacency is an oracle. -/

/- The target asserts a reduction, rather than a conditional implication from
an assumed reduction. -/

end OAI
