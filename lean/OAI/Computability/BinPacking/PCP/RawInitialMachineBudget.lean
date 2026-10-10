import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.PCP.RawInitialPredicate

namespace OAI

namespace BinPackingGames.Foundations.PCP.GenericGraphTables

open BinPackingGames.Foundations.Complexity

abbrev Label (q : Nat) := Fin q
abbrev RelationTable (q : Nat) := Vector Bool (q * q)

variable {q : Nat}

def relationIndex (q : Nat) : (Label q) × (Label q) ≃ Fin (q * q) := finProdFinEquiv

theorem relationIndex_val (a b : (Label q)) :
    ((relationIndex q) (a, b)).val = b.val + q * a.val := rfl

def relationAt (table : (RelationTable q)) (a b : (Label q)) : Bool :=
  table[(relationIndex q) (a, b)]

def relationOf (predicate : (Label q) → (Label q) → Bool) : (RelationTable q) :=
  Vector.ofFn (fun i => predicate ((relationIndex q).symm i).1 ((relationIndex q).symm i).2)

@[simp] theorem relationAt_relationOf (predicate : (Label q) → (Label q) → Bool) (a b : (Label q)) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

structure DartRow (q vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : (RelationTable q)

abbrev Rows (q vertices darts : Nat) := Vector (DartRow q vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows q n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows q n m) (e : Fin m) (a b : (Label q)) : Bool :=
  relationAt rows[e].relation a b

def Valid {n m : Nat} (rows : Rows q n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

instance {n m : Nat} (rows : Rows q n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

structure Table (q : Nat) where
  vertices : Nat
  darts : Nat
  rows : Rows q vertices darts
  valid : Valid rows

def rowList (table : (Table q)) : List (DartRow q table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : (Table q)) : (rowList table).length = table.darts := by
  simp [rowList]

def semantics (table : (Table q)) : ConstraintGraph (Fin table.vertices) (Fin table.darts) (Label q) where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : (Table q)) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : (Table q)) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : (Table q)) (e : Fin table.darts) (a b : (Label q)) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : Rows q n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : (Table q) :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

private theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) :
    ConstraintGraph (Fin n) (Fin m) (Label q) where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

theorem enumeratedGraph_rejectionCount {V E A : Type*} [Fintype E] {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).rejectionCount
      (fun v => labelOrder (labeling (vertexOrder.symm v))) = G.rejectionCount labeling := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv dartOrder
  intro e
  simp only [ConstraintGraph.mem_rejectedDarts, enumeratedGraph_edgeSatisfied]

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) : (Table q) :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

def bitWord (b : Bool) : Nat := if b then 1 else 0

def parseBit : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

@[simp] theorem parseBit_bitWord (b : Bool) : parseBit (bitWord b) = some b := by
  cases b <;> rfl

@[simp] theorem parseBits_bitWords (bits : List Bool) :
    (bits.map bitWord).mapM parseBit = some bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [ih]

def relationWords (relation : (RelationTable q)) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : (RelationTable q)) :
    (relationWords relation).length = (q * q) := by simp [relationWords]

def parseRelation (q : Nat) (words : List Nat) : Option (RelationTable q) := do
  let bits ← words.mapM parseBit
  if length_ok : bits.length = (q * q) then
    some ⟨bits.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseRelation_encoded (relation : (RelationTable q)) :
    (parseRelation q) (relationWords relation) = some relation := by
  unfold parseRelation relationWords
  rw [parseBits_bitWords]
  simp
  exact Vector.toArray_toList

def rowWords {n m : Nat} (row : DartRow q n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

def parseRow (q : Nat) (vertices darts : Nat) : List Nat → Option (DartRow q vertices darts × List Nat)
  | tail :: reverseIndex :: words => do
      let tail ← parseLabel vertices tail
      let reverseIndex ← parseLabel darts reverseIndex
      let relation ← (parseRelation q) (words.take (q * q))
      return (⟨tail, reverseIndex, relation⟩, words.drop (q * q))
  | _ => none

@[simp] theorem parseRow_encoded {n m : Nat} (row : DartRow q n m) (rest : List Nat) :
    (parseRow q) n m (rowWords row ++ rest) = some (row, rest) := by
  cases row with
  | mk tail reverseIndex relation =>
      have taken := List.take_left' (l₂ := rest) (relationWords_length relation)
      have dropped := List.drop_left' (l₂ := rest) (relationWords_length relation)
      simp [rowWords, parseRow, taken, dropped]

def parseRows (q : Nat) (vertices darts : Nat) :
    Nat → List Nat → Option (List (DartRow q vertices darts) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (row, words) ← (parseRow q) vertices darts words
      let (rows, words) ← (parseRows q) vertices darts count words
      return (row :: rows, words)

@[simp] theorem parseRows_encoded {n m : Nat} (rows : List (DartRow q n m)) (rest : List Nat) :
    (parseRows q) n m rows.length (rows.flatMap rowWords ++ rest) = some (rows, rest) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [parseRows, List.append_assoc, ih]

def tableWords (table : (Table q)) : List Nat :=
  [table.vertices, table.darts] ++ (rowList table).flatMap rowWords

def tableBits (table : (Table q)) : List Bool := encodeWords (tableWords table)

def decodeTableWords (q : Nat) : List Nat → Option (Table q)
  | vertices :: darts :: words => do
      let (parsed, trailing) ← (parseRows q) vertices darts darts words
      if trailing = [] then
        if length_ok : parsed.length = darts then
          let rows : Rows q vertices darts := ⟨parsed.toArray, by simpa using length_ok⟩
          if valid : Valid rows then some ⟨vertices, darts, rows, valid⟩ else none
        else none
      else none
  | _ => none

@[simp] theorem decodeTableWords_encoded (table : (Table q)) :
    (decodeTableWords q) (tableWords table) = some table := by
  cases table with
  | mk vertices darts rows valid =>
      have parsed := parseRows_encoded rows.toList []
      simp only [Vector.length_toList, List.append_nil] at parsed
      simp [tableWords, rowList, decodeTableWords, parsed, valid, Vector.toArray_toList]

def decodeTableBits (q : Nat) (bits : List Bool) : Option (Table q) :=
  decodeWords bits >>= (decodeTableWords q)

@[simp] theorem decodeTableBits_encoded (table : (Table q)) :
    (decodeTableBits q) (tableBits table) = some table := by
  simp [decodeTableBits, tableBits]

def encoding (q : Nat) : Computability.Encoding (Table q) Bool where
  encode := tableBits
  decode := (decodeTableBits q)
  decode_encode := decodeTableBits_encoded

theorem tableBits_injective : Function.Injective (tableBits (q := q)) := (encoding q).encode_injective

@[simp] theorem rowWords_length {n m : Nat} (row : DartRow q n m) :
    (rowWords row).length = (q * q + 2) := by
  simp only [rowWords, List.length_append, List.length_cons, List.length_nil,
    relationWords_length]
  omega

theorem rowsWords_length {n m : Nat} (rows : List (DartRow q n m)) :
    (rows.flatMap rowWords).length = (q * q + 2) * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [ih, Nat.mul_add, Nat.add_comm]

@[simp] theorem tableWords_length (table : (Table q)) :
    (tableWords table).length = 2 + (q * q + 2) * table.darts := by
  simp only [tableWords, List.length_append, List.length_cons, List.length_nil,
    rowsWords_length, rowList_length]

theorem tableWords_length_le_bits (table : (Table q)) :
    2 + (q * q + 2) * table.darts ≤ (tableBits table).length := by
  rw [tableBits, encodeWords_length, ← tableWords_length]
  omega

theorem relationBits_length_le (relation : (RelationTable q)) :
    (encodeWords (relationWords relation)).length ≤ (2 * (q * q)) := by
  have h := encodeWords_length_le (relationWords relation) 1 (by
    intro word hword
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp hword
    cases bit <;> decide)
  simpa only [relationWords_length, Nat.mul_comm] using h

theorem rowBits_length_le {n m : Nat} (row : DartRow q n m) :
    (encodeWords (rowWords row)).length ≤ n + m + (2 * (q * q)) := by
  have ht := row.tail.isLt
  have hr := row.reverseIndex.isLt
  have hp := relationBits_length_le row.relation
  simp only [rowWords, encodeWords_append, List.length_append, encodeWords,
    encodeWord_length, List.length_nil] at ⊢
  omega

theorem rowsBits_length_le {n m : Nat} (rows : List (DartRow q n m)) :
    (encodeWords (rows.flatMap rowWords)).length ≤ rows.length * (n + m + (2 * (q * q))) := by
  induction rows with
  | nil => simp [encodeWords]
  | cons row rows ih =>
      have hrow := rowBits_length_le row
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem tableBits_length_le (table : (Table q)) :
    (tableBits table).length ≤ table.vertices + table.darts + 2 +
      table.darts * (table.vertices + table.darts + (2 * (q * q))) := by
  have hrows := rowsBits_length_le (rowList table)
  rw [rowList_length] at hrows
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem vertices_le_tableBits_length (table : (Table q)) :
    table.vertices ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem darts_le_tableBits_length (table : (Table q)) :
    table.darts ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end BinPackingGames.Foundations.PCP.GenericGraphTables

namespace BinPackingGames.Foundations.PCP.GraphTableComplexity

open BinPackingGames.Foundations.Complexity
open Polynomial

noncomputable def encodingPolynomial (q : Nat) : Polynomial Nat :=
  X ^ 2 + C (2 * (q * q) + 1) * X + C 2

theorem encodingPolynomial_eval (q n : Nat) :
    (encodingPolynomial q).eval n = n ^ 2 + (2 * (q * q) + 1) * n + 2 := by
  simp [encodingPolynomial]

theorem encodingPolynomial_mono (q : Nat) {n m : Nat} (hnm : n ≤ m) :
    (encodingPolynomial q).eval n ≤ (encodingPolynomial q).eval m := by
  rw [encodingPolynomial_eval, encodingPolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.pow_le_pow_left hnm 2) (Nat.mul_le_mul_left _ hnm)) 2

theorem rowBound_le_polynomial (q vertices darts : Nat) :
    vertices + darts + 2 + darts * (vertices + darts + 2 * (q * q)) ≤
      (encodingPolynomial q).eval (vertices + darts) := by
  have hd : darts ≤ vertices + darts := Nat.le_add_left darts vertices
  calc
    _ ≤ vertices + darts + 2 +
        (vertices + darts) * (vertices + darts + 2 * (q * q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
    _ = _ := by rw [encodingPolynomial_eval]; ring

theorem generic_size_add_two_le_bits {q : Nat} (table : GenericGraphTables.Table q) :
    table.vertices + table.darts + 2 ≤ (GenericGraphTables.tableBits table).length := by
  simp only [GenericGraphTables.tableBits, GenericGraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

theorem generic_bits_le_polynomial {q : Nat} (table : GenericGraphTables.Table q) :
    (GenericGraphTables.tableBits table).length ≤
      (encodingPolynomial q).eval (table.vertices + table.darts) :=
  (GenericGraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial q table.vertices table.darts)

theorem generic_bits_le_of_size_le {q N : Nat} (table : GenericGraphTables.Table q)
    (hsize : table.vertices + table.darts ≤ N) :
    (GenericGraphTables.tableBits table).length ≤ (encodingPolynomial q).eval N :=
  (generic_bits_le_polynomial table).trans (encodingPolynomial_mono q hsize)

theorem size_add_two_le_bits (table : GraphTables.Table) :
    table.vertices + table.darts + 2 ≤ (GraphTables.tableBits table).length := by
  simp only [GraphTables.tableBits, GraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

theorem bits_le_polynomial (table : GraphTables.Table) :
    (GraphTables.tableBits table).length ≤
      (encodingPolynomial 64).eval (table.vertices + table.darts) :=
  (GraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial 64 table.vertices table.darts)

theorem bits_le_of_size_le {N : Nat} (table : GraphTables.Table)
    (hsize : table.vertices + table.darts ≤ N) :
    (GraphTables.tableBits table).length ≤ (encodingPolynomial 64).eval N :=
  (bits_le_polynomial table).trans (encodingPolynomial_mono 64 hsize)

end BinPackingGames.Foundations.PCP.GraphTableComplexity

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Input

open BinPackingGames.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationIndex_val relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords rowWords_length
  rowsWords_length tableWords tableWords_length tableBits encoding
  parseRelation parseRow parseRows decodeTableWords decodeTableBits
  parseRelation_encoded parseRow_encoded parseRows_encoded
  decodeTableWords_encoded decodeTableBits_encoded tableBits_injective
  relationBits_length_le rowBits_length_le rowsBits_length_le tableWords_length_le_bits
  tableBits_length_le vertices_le_tableBits_length darts_le_tableBits_length)

variable {q n m : Nat}

abbrev rowWidth (q : Nat) : Nat := q * q + 2

def rowOffset (q e : Nat) : Nat := 2 + rowWidth q * e

theorem rowsWords_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    rows.flatMap rowWords = (rows.take e).flatMap rowWords ++
      (rowWords rows[e] ++ (rows.drop (e + 1)).flatMap rowWords) := by
  have hs : rows.take e ++ rows[e] :: rows.drop (e + 1) = rows := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow q n m) => rs.flatMap rowWords) hs
  simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using hw.symm

theorem rowsBits_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    encodeWords (rows.flatMap rowWords) =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          encodeWords ((rows.drop (e + 1)).flatMap rowWords)) := by
  rw [rowsWords_split rows e he]
  simp only [encodeWords_append]

theorem rowsBits_append_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) (suffix : List Bool) :
    encodeWords (rows.flatMap rowWords) ++ suffix =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          (encodeWords ((rows.drop (e + 1)).flatMap rowWords) ++ suffix)) := by
  rw [rowsBits_split rows e he]
  simp only [List.append_assoc]

def prefixWords (table : Table q) (e : Fin table.darts) : List Nat :=
  [table.vertices, table.darts] ++ ((rowList table).take e.val).flatMap rowWords

def suffixWords (table : Table q) (e : Fin table.darts) : List Nat :=
  ((rowList table).drop (e.val + 1)).flatMap rowWords

theorem prefixWords_length (table : Table q) (e : Fin table.darts) :
    (prefixWords table e).length = rowOffset q e.val := by
  simp [prefixWords, rowOffset, rowWidth, Nat.mul_comm, Nat.add_comm]
  omega

theorem tableWords_at_row (table : Table q) (e : Fin table.darts) :
    tableWords table = prefixWords table e ++
      (rowWords table.rows[e] ++ suffixWords table e) := by
  have hs := rowsWords_split (rowList table) e.val (by simpa only [rowList_length] using e.isLt)
  simp only [rowList, Vector.getElem_toList] at hs
  unfold tableWords prefixWords suffixWords rowList
  rw [hs]
  simp only [List.append_assoc, Fin.getElem_fin]

theorem tableBits_at_row (table : Table q) (e : Fin table.darts) :
    tableBits table = encodeWords (prefixWords table e) ++
      (encodeWords (rowWords table.rows[e]) ++ encodeWords (suffixWords table e)) := by
  rw [tableBits, tableWords_at_row table e]
  simp only [encodeWords_append]

theorem tableBits_header (table : Table q) :
    tableBits table = encodeWord table.vertices ++
      (encodeWord table.darts ++ encodeWords ((rowList table).flatMap rowWords)) := by
  simp [tableBits, tableWords, encodeWords]

theorem tableWords_drop_row (table : Table q) (e : Fin table.darts) :
    (tableWords table).drop (rowOffset q e.val) =
      rowWords table.rows[e] ++ suffixWords table e := by
  rw [tableWords_at_row table e]
  exact List.drop_left' (l₂ := rowWords table.rows[e] ++ suffixWords table e)
    (prefixWords_length table e)

theorem tableWords_take_row (table : Table q) (e : Fin table.darts) :
    ((tableWords table).drop (rowOffset q e.val)).take (rowWidth q) =
      rowWords table.rows[e] := by
  rw [tableWords_drop_row]
  exact List.take_left' (l₂ := suffixWords table e) (rowWords_length table.rows[e])

theorem tableWords_get_tail (table : Table q) (e : Fin table.darts) :
    (tableWords table)[rowOffset q e.val]? = some table.rows[e].tail.val := by
  have h := congrArg (fun words : List Nat => words[0]?) (tableWords_drop_row table e)
  simpa [List.getElem?_drop, rowWords] using h

theorem tableWords_get_reverse (table : Table q) (e : Fin table.darts) :
    (tableWords table)[rowOffset q e.val + 1]? = some table.rows[e].reverseIndex.val := by
  have h := congrArg (fun words : List Nat => words[1]?) (tableWords_drop_row table e)
  simpa [List.getElem?_drop, rowWords] using h

theorem tableWords_drop_relation (table : Table q) (e : Fin table.darts) :
    (tableWords table).drop (rowOffset q e.val + 2) =
      relationWords table.rows[e].relation ++ suffixWords table e := by
  rw [← List.drop_drop, tableWords_drop_row]
  simp [rowWords]

theorem relationWords_get (relation : RelationTable q) (j : Fin (q * q)) :
    (relationWords relation)[j.val]? = some (bitWord relation[j]) := by
  rw [List.getElem?_eq_getElem (by simpa only [relationWords_length] using j.isLt)]
  simp [relationWords]

theorem tableWords_get_relation (table : Table q) (e : Fin table.darts)
    (j : Fin (q * q)) :
    (tableWords table)[rowOffset q e.val + 2 + j.val]? =
      some (bitWord table.rows[e].relation[j]) := by
  have h := congrArg (fun words : List Nat => words[j.val]?)
    (tableWords_drop_relation table e)
  rw [List.getElem?_drop,
    List.getElem?_append_left (by simpa only [relationWords_length] using j.isLt), relationWords_get] at h
  exact h

theorem tableWords_get_predicate (table : Table q) (e : Fin table.darts)
    (a b : Label q) :
    (tableWords table)[rowOffset q e.val + 2 + (b.val + q * a.val)]? =
      some (bitWord ((semantics table).accepts e a b)) := by
  simpa only [relationIndex_val, semantics_accepts, relationAt] using
    tableWords_get_relation table e ((relationIndex q) (a, b))

theorem rowOffset_lt_length (table : Table q) (e : Fin table.darts) :
    rowOffset q e.val < (tableWords table).length := by
  rw [tableWords_length]
  have h := Nat.mul_le_mul_left (rowWidth q) (Nat.succ_le_of_lt e.isLt)
  rw [Nat.mul_succ] at h
  unfold rowOffset rowWidth at *
  omega

theorem relationOffset_lt_length (table : Table q) (e : Fin table.darts)
    (j : Fin (q * q)) :
    rowOffset q e.val + 2 + j.val < (tableWords table).length := by
  rw [tableWords_length]
  have h := Nat.mul_le_mul_left (rowWidth q) (Nat.succ_le_of_lt e.isLt)
  rw [Nat.mul_succ] at h
  have hj := j.isLt
  unfold rowOffset rowWidth at *
  omega

end BinPackingGames.Foundations.PCP.AlphabetTable.Input

namespace BinPackingGames.Foundations.PCP.RawInitialMachineBudget

open Target Complexity

def nameSum {n : Nat} (c : Clause n) : Nat :=
  (c)[0].variableIndex.val + (c)[1].variableIndex.val + (c)[2].variableIndex.val

def bodyTime {n : Nat} (i : Nat) (c : Clause n) : Nat :=
  6 * n + 18 * i + 2 * nameSum c +
    2 * (encodeWords (Complexity.clauseWords c)).length + 63

def loopTime {n : Nat} (i : Nat) : List (Clause n) → Nat
  | [] => 1
  | c :: cs => bodyTime i c + loopTime (i + 1) cs

theorem nameSum_le {n : Nat} (c : Clause n) : nameSum c ≤ 3 * n := by
  have h0 := (c)[0].variableIndex.isLt
  have h1 := (c)[1].variableIndex.isLt
  have h2 := (c)[2].variableIndex.isLt
  unfold nameSum
  omega

theorem bodyTime_le {n : Nat} (i : Nat) (c : Clause n) :
    bodyTime i c ≤ 18 * n + 18 * i + 81 := by
  have hn := nameSum_le c
  have hb := clauseBits_length_le c
  unfold bodyTime
  omega

theorem loopTime_le {n : Nat} (i : Nat) (cs : List (Clause n)) :
    loopTime i cs ≤ cs.length * (18 * n + 18 * (i + cs.length) + 81) + 1 := by
  induction cs generalizing i with
  | nil => simp [loopTime]
  | cons c cs ih =>
      have hc := bodyTime_le i c
      have ht := ih (i + 1)
      have hbound : bodyTime i c ≤ 18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      have hsame : 18 * n + 18 * (i + 1 + cs.length) + 81 =
          18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      rw [hsame] at ht
      rw [loopTime]
      calc
        _ ≤ (18 * n + 18 * (i + (c :: cs).length) + 81) +
            (cs.length * (18 * n + 18 * (i + (c :: cs).length) + 81) + 1) :=
          Nat.add_le_add hbound ht
        _ = _ := by rw [List.length_cons]; ring

theorem input_header_bound (F : Formula) :
    F.variables + F.clauses.length + 2 ≤ (formulaBits F).length := by
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem graph_size_bound (F : Formula) :
    (RawInitialTables.table F).vertices + (RawInitialTables.table F).darts ≤
      7 * (formulaBits F).length := by
  rw [RawInitialTables.initial_size]
  have h := input_header_bound F
  omega

def fullBudget (F : Formula) : Nat :=
  6 * F.variables + 10 * F.clauses.length + 30 + loopTime 0 F.clauses +
    (GraphTables.tableBits (RawInitialTables.table F)).length

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * Polynomial.X ^ 2 + Polynomial.C 60000 * Polynomial.X +
    Polynomial.C 100

theorem timePolynomial_eval (N : Nat) :
    timePolynomial.eval N = 100 * N ^ 2 + 60000 * N + 100 := by
  simp [timePolynomial]

theorem fullBudget_le (F : Formula) :
    fullBudget F ≤ timePolynomial.eval (formulaBits F).length := by
  have hinput := input_header_bound F
  have hloop := loopTime_le 0 F.clauses
  have hout := GraphTableComplexity.bits_le_of_size_le (RawInitialTables.table F)
    (graph_size_bound F)
  rw [GraphTableComplexity.encodingPolynomial_eval] at hout
  simp only [Nat.zero_add] at hloop
  have hm : F.clauses.length ≤ (formulaBits F).length := by omega
  have hcoefficient : 18 * F.variables + 18 * F.clauses.length + 81 ≤
      18 * (formulaBits F).length + 81 := by omega
  have hproduct := Nat.mul_le_mul hm hcoefficient
  rw [timePolynomial_eval]
  unfold fullBudget
  nlinarith

end BinPackingGames.Foundations.PCP.RawInitialMachineBudget

end OAI
