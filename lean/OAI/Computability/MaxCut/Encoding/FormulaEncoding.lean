import Mathlib
import OAI.Computability.MaxCut.Encoding.Serialization

namespace OAI

/-! A checked parser for the concrete 3CNF serialization, including finite-index
bounds, Boolean signs, clause count, and absence of trailing garbage. -/

namespace MaxCutGames.Foundations.Complexity

open Target

def parseLiteral («variables» : Nat) : List Nat → Option (Literal «variables» × List Nat)
  | index :: sign :: rest =>
      if bounded : index < «variables» then
        if sign = 0 then some (⟨⟨index, bounded⟩, false⟩, rest)
        else if sign = 1 then some (⟨⟨index, bounded⟩, true⟩, rest)
        else none
      else none
  | _ => none

@[simp] theorem parseLiteral_encoded {n : Nat} (literal : Literal n) (rest : List Nat) :
    parseLiteral n (literalWords literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk index positive =>
      cases positive <;> simp [literalWords, parseLiteral, index.isLt]

def parseClause («variables» : Nat) (words : List Nat) : Option (Clause «variables» × List Nat) := do
  let (a, words) ← parseLiteral «variables» words
  let (b, words) ← parseLiteral «variables» words
  let (c, words) ← parseLiteral «variables» words
  return (⟨#[a, b, c], rfl⟩, words)

theorem clause_three_entries {n : Nat} (clause : Clause n) :
    (⟨#[clause[0], clause[1], clause[2]], rfl⟩ : Clause n) = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded {n : Nat} (clause : Clause n) (rest : List Nat) :
    parseClause n (clauseWords clause ++ rest) = some (clause, rest) := by
  simp [clauseWords, List.append_assoc, parseClause, parseLiteral_encoded,
    clause_three_entries]

def parseClauses («variables» : Nat) : Nat → List Nat → Option (List (Clause «variables») × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (clause, words) ← parseClause «variables» words
      let (clauses, words) ← parseClauses «variables» count words
      return (clause :: clauses, words)

@[simp] theorem parseClauses_encoded {n : Nat} (clauses : List (Clause n)) (rest : List Nat) :
    parseClauses n clauses.length (clauses.flatMap clauseWords ++ rest) = some (clauses, rest) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp [List.append_assoc, parseClauses, parseClause_encoded, ih]

def decodeFormulaWords : List Nat → Option Formula
  | «variables» :: count :: words => do
      let (clauses, trailing) ← parseClauses «variables» count words
      if trailing = [] then some ⟨«variables», clauses⟩ else none
  | _ => none

@[simp] theorem decodeFormulaWords_encoded (formula : Formula) :
    decodeFormulaWords (formulaWords formula) = some formula := by
  cases formula with
  | mk «variables» clauses =>
      have parsed := parseClauses_encoded clauses []
      simp only [List.append_nil] at parsed
      simp [decodeFormulaWords, formulaWords, parsed]

def decodeFormulaBits (bits : List Bool) : Option Formula :=
  decodeWords bits >>= decodeFormulaWords

@[simp] theorem decodeFormulaBits_encoded (formula : Formula) :
    decodeFormulaBits (formulaBits formula) = some formula := by
  simp [decodeFormulaBits, formulaBits]

theorem formulaBits_injective {first second : Formula}
    (same : formulaBits first = formulaBits second) : first = second := by
  have parsed := congrArg decodeFormulaBits same
  simpa only [decodeFormulaBits_encoded, Option.some.injEq] using parsed

/-! Concrete forward-table serialization of unique games. The parser reconstructs
an inverse by finite search and checks both inverse laws. Constraint occurrences,
including repeated parallel edges, are preserved in their original list order. -/

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

@[simp] theorem parseLabel_value {q : Nat} (label : Fin q) :
    parseLabel q label.val = some label := by simp [parseLabel, label.isLt]

@[simp] theorem parseLabels_values {q : Nat} (labels : List (Fin q)) :
    (labels.map Fin.val).mapM (parseLabel q) = some labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp [ih]

def parseImages (alphabet : Nat) (words : List Nat) : Option (Vector (Fin alphabet) alphabet) := do
  let labels ← words.mapM (parseLabel alphabet)
  if length_ok : labels.length = alphabet then
    some ⟨labels.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseImages_values {q : Nat} (images : Vector (Fin q) q) :
    parseImages q (images.toList.map Fin.val) = some images := by
  unfold parseImages
  rw [parseLabels_values]
  simp
  exact Vector.toArray_toList

def findPreimage {q : Nat} (images : Vector (Fin q) q) (label : Fin q) : Fin q :=
  ((List.finRange q).find? (fun x => decide (images[x] = label))).getD label

theorem findPreimage_permutation {q : Nat} (table : PermutationTable q) (label : Fin q) :
    findPreimage table.images label = table.inverseImages[label] := by
  have exists_preimage :
      ((List.finRange q).find? (fun x => decide (table.images[x] = label))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨table.inverseImages[label], List.mem_finRange _, by
      simpa only [decide_eq_true_eq] using table.rightInverse label⟩
  cases found : (List.finRange q).find? (fun x => decide (table.images[x] = label)) with
  | none =>
      rw [found] at exists_preimage
      contradiction
  | some x =>
      have image_eq : table.images[x] = label := by
        simpa using List.find?_some found
      have x_eq := table.images_injective (image_eq.trans (table.rightInverse label).symm)
      unfold findPreimage
      rw [found]
      exact x_eq

def searchedInverse {q : Nat} (images : Vector (Fin q) q) : Vector (Fin q) q :=
  Vector.ofFn (findPreimage images)

theorem searchedInverse_permutation {q : Nat} (table : PermutationTable q) :
    searchedInverse table.images = table.inverseImages := by
  apply Vector.ext
  intro i hi
  simpa [searchedInverse] using findPreimage_permutation table ⟨i, hi⟩

def tableWords {q : Nat} (table : PermutationTable q) : List Nat :=
  table.images.toList.map Fin.val

def parsePermutation (alphabet : Nat) (words : List Nat) : Option (PermutationTable alphabet) := do
  let images ← parseImages alphabet words
  let inverseImages := searchedInverse images
  if left : ∀ label : Fin alphabet, inverseImages[images[label]] = label then
    if right : ∀ label : Fin alphabet, images[inverseImages[label]] = label then
      some ⟨images, inverseImages, left, right⟩
    else none
  else none

@[simp] theorem parsePermutation_encoded {q : Nat} (table : PermutationTable q) :
    parsePermutation q (tableWords table) = some table := by
  simp only [parsePermutation, tableWords, parseImages_values]
  dsimp only [Bind.bind, Option.bind]
  simp only [searchedInverse_permutation]
  simp only [table.leftInverse, table.rightInverse, implies_true, dite_true]

@[simp] theorem tableWords_length {q : Nat} (table : PermutationTable q) :
    (tableWords table).length = q := by simp [tableWords]

def constraintWords {n q : Nat} (constraint : Constraint n q) : List Nat :=
  [constraint.source.val, constraint.target.val] ++ tableWords constraint.permutation

def parseConstraint (vertices alphabet : Nat) :
    List Nat → Option (Constraint vertices alphabet × List Nat)
  | source :: target :: words => do
      let source ← parseLabel vertices source
      let target ← parseLabel vertices target
      let permutation ← parsePermutation alphabet (words.take alphabet)
      return (⟨source, target, permutation⟩, words.drop alphabet)
  | _ => none

@[simp] theorem parseConstraint_encoded {n q : Nat}
    (constraint : Constraint n q) (rest : List Nat) :
    parseConstraint n q (constraintWords constraint ++ rest) = some (constraint, rest) := by
  cases constraint with
  | mk source target permutation =>
      have taken := List.take_left' (l₂ := rest) (tableWords_length permutation)
      have dropped := List.drop_left' (l₂ := rest) (tableWords_length permutation)
      simp [constraintWords, parseConstraint, taken, dropped]

def parseConstraints (vertices alphabet : Nat) :
    Nat → List Nat → Option (List (Constraint vertices alphabet) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (constraint, words) ← parseConstraint vertices alphabet words
      let (constraints, words) ← parseConstraints vertices alphabet count words
      return (constraint :: constraints, words)

@[simp] theorem parseConstraints_encoded {n q : Nat}
    (constraints : List (Constraint n q)) (rest : List Nat) :
    parseConstraints n q constraints.length (constraints.flatMap constraintWords ++ rest) =
      some (constraints, rest) := by
  induction constraints with
  | nil => rfl
  | cons constraint constraints ih =>
      simp [parseConstraints, List.append_assoc, ih]

def gameWords {q : Nat} (game : Instance q) : List Nat :=
  [game.vertices, q, game.constraints.length] ++ game.constraints.flatMap constraintWords

def gameBits {q : Nat} (game : Instance q) : List Bool := encodeWords (gameWords game)

def decodeGameWords (alphabet : Nat) : List Nat → Option (Instance alphabet)
  | vertices :: encodedAlphabet :: count :: words => do
      if encodedAlphabet = alphabet then
        let (constraints, trailing) ← parseConstraints vertices alphabet count words
        if trailing = [] then
          if nonempty : constraints ≠ [] then some ⟨vertices, constraints, nonempty⟩ else none
        else none
      else none
  | _ => none

@[simp] theorem decodeGameWords_encoded {q : Nat} (game : Instance q) :
    decodeGameWords q (gameWords game) = some game := by
  cases game with
  | mk vertices constraints nonempty =>
      have parsed := parseConstraints_encoded constraints []
      simp only [List.append_nil] at parsed
      simp [decodeGameWords, gameWords, parsed, nonempty]

def decodeGameBits (alphabet : Nat) (bits : List Bool) : Option (Instance alphabet) :=
  decodeWords bits >>= decodeGameWords alphabet

@[simp] theorem decodeGameBits_encoded {q : Nat} (game : Instance q) :
    decodeGameBits q (gameBits game) = some game := by
  simp [decodeGameBits, gameBits]

theorem gameBits_injective {q : Nat} {first second : Instance q}
    (same : gameBits first = gameBits second) : first = second := by
  have parsed := congrArg (decodeGameBits q) same
  simpa only [decodeGameBits_encoded, Option.some.injEq] using parsed

@[simp] theorem constraintWords_length {n q : Nat} (constraint : Constraint n q) :
    (constraintWords constraint).length = q + 2 := by simp [constraintWords]

theorem constraintsWords_length {n q : Nat} (constraints : List (Constraint n q)) :
    (constraints.flatMap constraintWords).length = constraints.length * (q + 2) := by
  induction constraints with
  | nil => simp
  | cons constraint constraints ih =>
      simp only [List.flatMap_cons, List.length_append, constraintWords_length,
        List.length_cons, Nat.add_mul, Nat.one_mul, ih]
      omega

@[simp] theorem gameWords_length {q : Nat} (game : Instance q) :
    (gameWords game).length = 3 + game.constraints.length * (q + 2) := by
  simp only [gameWords, List.length_append, List.length_cons, List.length_nil,
    constraintsWords_length]

end MaxCutGames.Foundations.Complexity

end OAI
