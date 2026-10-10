import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Logic.Function.Iterate
import OAI.Computability.BinPacking.Model
import OAI.Computability.BinPacking.Reductions.Target

namespace OAI

namespace BinPackingGames.Foundations.Complexity

section

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
  [formula.variables, formula.clauses.length] ++ formula.clauses.flatMap clauseWords

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
      formula.variables + formula.clauses.length + 2 +
        formula.clauses.length * (3 * (formula.variables + 2)) := by
  have h := clausesBits_length_le formula.clauses
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end

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

end BinPackingGames.Foundations.Complexity

namespace BinPackingGames.Foundations.Complexity.MachineLookupSpec

def skipWord : List Bool → List Bool
  | [] => []
  | true :: bs => skipWord bs
  | false :: bs => bs

@[simp] theorem skipWord_encodeWord (n : Nat) (bs : List Bool) :
    skipWord (encodeWord n ++ bs) = bs := by
  induction n with
  | zero => simp [encodeWord, skipWord]
  | succ n ih =>
    simpa [encodeWord, List.replicate_succ, skipWord] using ih

theorem skipWord_iterate_encodeWords (i : Nat) (values : List Nat) :
    (skipWord^[i]) (encodeWords values) = encodeWords (values.drop i) := by
  induction i generalizing values with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases values with
    | nil => simpa [encodeWords, skipWord] using ih []
    | cons n ns =>
      simpa only [encodeWords, skipWord_encodeWord, List.drop_succ_cons] using ih ns

def headWord : List Bool → Option (List Bool)
  | [] => none
  | false :: _ => some [false]
  | true :: bs => (headWord bs).map (true :: ·)

@[simp] theorem headWord_encodeWord (n : Nat) (bs : List Bool) :
    headWord (encodeWord n ++ bs) = some (encodeWord n) := by
  induction n with
  | zero => simp [encodeWord, headWord]
  | succ n ih =>
    simpa [encodeWord, List.replicate_succ, headWord] using
      congrArg (Option.map (true :: ·)) ih

@[simp] theorem headWord_encodeWords (values : List Nat) :
    headWord (encodeWords values) = values.head?.map encodeWord := by
  cases values with
  | nil => rfl
  | cons n ns => exact headWord_encodeWord n (encodeWords ns)

def lookupBits (i : Nat) (table : List Bool) : Option (List Bool) :=
  headWord ((skipWord^[i]) table)

@[simp] theorem lookupBits_encodeWords (i : Nat) (values : List Nat) :
    lookupBits i (encodeWords values) = values[i]?.map encodeWord := by
  rw [lookupBits, skipWord_iterate_encodeWords, headWord_encodeWords,
    List.head?_drop]

def lookupEncoded (index table : List Bool) : Option (List Bool) :=
  match decodeWords index with
  | some [i] => lookupBits i table
  | _ => none

@[simp] theorem decodeWords_encodeWord (i : Nat) :
    decodeWords (encodeWord i) = some [i] := by
  simpa [encodeWords] using decodeWords_encodeWords [i]

@[simp] theorem lookupEncoded_encode (i : Nat) (values : List Nat) :
    lookupEncoded (encodeWord i) (encodeWords values) =
      values[i]?.map encodeWord := by
  simp [lookupEncoded]

theorem lookupEncoded_some (i value : Nat) (values : List Nat)
    (h : values[i]? = some value) :
    lookupEncoded (encodeWord i) (encodeWords values) = some (encodeWord value) := by
  simp [h]

theorem lookupEncoded_none (i : Nat) (values : List Nat)
    (h : values.length ≤ i) :
    lookupEncoded (encodeWord i) (encodeWords values) = none := by
  simp [List.getElem?_eq_none h]

theorem encoded_selected_split (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    encodeWords values = encodeWords (values.take i) ++ encodeWord value ++
      encodeWords (values.drop (i + 1)) := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  have hs : values = values.take i ++ value :: values.drop (i + 1) := by
    calc
      values = values.take i ++ values.drop i := (List.take_append_drop i values).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hv]
  simpa only [encodeWords_append, encodeWords, List.append_assoc] using
    congrArg encodeWords hs

def scannedBits (values : List Nat) (i : Nat) : Nat :=
  (encodeWords (values.take (i + 1))).length

theorem encoded_prefix_length_le (values : List Nat) (i : Nat) :
    (encodeWords (values.take i)).length ≤ (encodeWords values).length := by
  have hs : encodeWords (values.take i) ++ encodeWords (values.drop i) =
      encodeWords values := by
    rw [← encodeWords_append, List.take_append_drop]
  have hl := congrArg List.length hs
  simp only [List.length_append] at hl
  omega

theorem scannedBits_le (values : List Nat) (i : Nat) :
    scannedBits values i ≤ (encodeWords values).length :=
  encoded_prefix_length_le values (i + 1)

theorem scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    scannedBits values i = (encodeWords (values.take i)).length + value + 1 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  simp [scannedBits, List.take_succ_eq_append_getElem hi, hv, encodeWords,
    Nat.add_assoc]

theorem selected_scan_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWords (values.take i)).length + value + 1 ≤
      (encodeWords values).length := by
  rw [← scannedBits_of_some values i value h]
  exact scannedBits_le values i

theorem output_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord value).length ≤ (encodeWords values).length := by
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

theorem index_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord i).length ≤ (encodeWords values).length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  have hp : i ≤ (encodeWords (values.take i)).length := by
    simp only [encodeWords_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

def steps : List Nat → Nat → Nat
  | [], i => 2 * i + 2
  | n :: _, 0 => n + 3
  | n :: ns, i + 1 => n + 2 + steps ns i

theorem steps_le_encoded_length_strong (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero =>
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega
    | succ i =>
      have ht := ih i
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega

theorem steps_le_encoded_length (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 3 := by
  have h := steps_le_encoded_length_strong values i
  omega

theorem steps_eq_scannedBits_of_lt (values : List Nat) (i : Nat)
    (h : i < values.length) :
    steps values i = scannedBits values i + i + 2 := by
  induction values generalizing i with
  | nil => simp at h
  | cons n ns ih =>
    cases i with
    | zero => simp [steps, scannedBits, encodeWords, Nat.add_assoc]
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [scannedBits] at ht
      simp only [steps, scannedBits, List.take_succ_cons, encodeWords,
        List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    steps values i = scannedBits values i + i + 2 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  exact steps_eq_scannedBits_of_lt values i hi

theorem steps_add_length_of_invalid (values : List Nat) (i : Nat)
    (h : values.length ≤ i) :
    steps values i + values.length = (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [steps, encodeWords, List.length_append, encodeWord_length,
        List.length_cons]
      omega

theorem steps_le_input_encoding_size (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * (encodeWord i).length := by
  have h := steps_le_encoded_length_strong values i
  rw [encodeWord_length]
  omega

end BinPackingGames.Foundations.Complexity.MachineLookupSpec

namespace BinPackingGames.Foundations.Complexity

def naturalWordsEncoding : Computability.Encoding (List Nat) Bool where
  encode := encodeWords
  decode := decodeWords
  decode_encode := decodeWords_encodeWords

def formulaEncoding : Computability.Encoding Target.Formula Bool where
  encode := formulaBits
  decode := decodeFormulaBits
  decode_encode := decodeFormulaBits_encoded

def gameEncoding (alphabet : Nat) : Computability.Encoding (Target.Instance alphabet) Bool where
  encode := gameBits
  decode := decodeGameBits alphabet
  decode_encode := decodeGameBits_encoded

def prefixBitMachine (bit : Bool) : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .push () (fun _ => bit) .halt

noncomputable def prefixBitPolyTime (bit : Bool) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id (bit :: ·) where
  tm := prefixBitMachine bit
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun bs := {
    steps := 1
    evals_in_steps := by
      change some (Turing.TM2.stepAux (.push () (fun _ => bit) .halt) ()
          (fun _ : Unit => bs.map id)) =
        some { l := none, var := (), stk := fun _ : Unit => (bit :: bs).map id }
      simp [Turing.TM2.stepAux]
      funext k
      cases k
      rfl
    steps_le_m := by simp
  }

def enlargePolynomialBound {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f)
    (bound : Polynomial Nat)
    (larger : ∀ n, certificate.time.eval n ≤ bound.eval n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  toTM2ComputableAux := certificate.toTM2ComputableAux
  time := bound
  outputsFun a := {
    toEvalsTo := (certificate.outputsFun a).toEvalsTo
    steps_le_m := Nat.le_trans (certificate.outputsFun a).steps_le_m (larger _)
  }

def composeMachinePhases {σ : Type} (step : σ → Option σ)
    (start intermediate : σ) (finish : Option σ)
    (p q : Polynomial Nat) (inputLength : Nat)
    (first : StateTransition.EvalsToInTime step start (some intermediate) (p.eval inputLength))
    (second : StateTransition.EvalsToInTime step intermediate finish (q.eval inputLength)) :
    StateTransition.EvalsToInTime step start finish ((p + q).eval inputLength) := by
  have composed := StateTransition.EvalsToInTime.trans step (p.eval inputLength)
    (q.eval inputLength) start intermediate finish first second
  simpa only [Polynomial.eval_add, Nat.add_comm] using composed

open Target

structure PolynomialGapReduction
    (completenessError soundnessError : RationalError)
    extends SemanticGapReduction completenessError soundnessError where
  computation : Turing.TM2ComputableInPolyTime formulaEncoding.encode
    (gameEncoding alphabet).encode reduce

end BinPackingGames.Foundations.Complexity

end OAI
