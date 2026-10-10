import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.ConstraintGraph
import OAI.Combinatorics.IndependentSets.Encoding.GameEncoding

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GraphTables

open IndependentSetsGames.Foundations.Complexity

abbrev Label := Fin 64
abbrev RelationTable := Vector Bool 4096

def relationIndex : Label × Label ≃ Fin 4096 := finProdFinEquiv

theorem relationIndex_val (a b : Label) :
    (relationIndex (a, b)).val = b.val + 64 * a.val := rfl

def relationAt (table : RelationTable) (a b : Label) : Bool :=
  table[relationIndex (a, b)]

def relationOf (predicate : Label → Label → Bool) : RelationTable :=
  Vector.ofFn (fun i => predicate (relationIndex.symm i).1 (relationIndex.symm i).2)

@[simp] theorem relationAt_relationOf (predicate : Label → Label → Bool) (a b : Label) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

structure DartRow (vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : RelationTable

abbrev Rows (vertices darts : Nat) := Vector (DartRow vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows n m) (e : Fin m) (a b : Label) : Bool :=
  relationAt rows[e].relation a b

def Valid {n m : Nat} (rows : Rows n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

instance {n m : Nat} (rows : Rows n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

structure Table where
  vertices : Nat
  darts : Nat
  rows : Rows vertices darts
  valid : Valid rows

def rowList (table : Table) : List (DartRow table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : Table) : (rowList table).length = table.darts := by
  simp [rowList]

def semantics (table : Table) : ConstraintGraph (Fin table.vertices) (Fin table.darts) Label where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : Table) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : Table) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : Table) (e : Fin table.darts) (a b : Label) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Rows n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Table :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
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
    (G : ConstraintGraph (Fin n) (Fin m) Label) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) :
    ConstraintGraph (Fin n) (Fin m) Label where
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
    (labelOrder : A ≃ Label) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

theorem enumeratedGraph_rejectionCount {V E A : Type*} [Fintype E] {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).rejectionCount
      (fun v => labelOrder (labeling (vertexOrder.symm v))) = G.rejectionCount labeling := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv dartOrder
  intro e
  simp only [ConstraintGraph.mem_rejectedDarts, enumeratedGraph_edgeSatisfied]

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) : Table :=
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

def relationWords (relation : RelationTable) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : RelationTable) :
    (relationWords relation).length = 4096 := by simp [relationWords]

def parseRelation (words : List Nat) : Option RelationTable := do
  let bits ← words.mapM parseBit
  if length_ok : bits.length = 4096 then
    some ⟨bits.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseRelation_encoded (relation : RelationTable) :
    parseRelation (relationWords relation) = some relation := by
  unfold parseRelation relationWords
  rw [parseBits_bitWords]
  simp
  exact Vector.toArray_toList

def rowWords {n m : Nat} (row : DartRow n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

def parseRow (vertices darts : Nat) : List Nat → Option (DartRow vertices darts × List Nat)
  | tail :: reverseIndex :: words => do
      let tail ← parseLabel vertices tail
      let reverseIndex ← parseLabel darts reverseIndex
      let relation ← parseRelation (words.take 4096)
      return (⟨tail, reverseIndex, relation⟩, words.drop 4096)
  | _ => none

@[simp] theorem parseRow_encoded {n m : Nat} (row : DartRow n m) (rest : List Nat) :
    parseRow n m (rowWords row ++ rest) = some (row, rest) := by
  cases row with
  | mk tail reverseIndex relation =>
      have taken := List.take_left' (l₂ := rest) (relationWords_length relation)
      have dropped := List.drop_left' (l₂ := rest) (relationWords_length relation)
      simp [rowWords, parseRow, taken, dropped]

def parseRows (vertices darts : Nat) :
    Nat → List Nat → Option (List (DartRow vertices darts) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (row, words) ← parseRow vertices darts words
      let (rows, words) ← parseRows vertices darts count words
      return (row :: rows, words)

@[simp] theorem parseRows_encoded {n m : Nat} (rows : List (DartRow n m)) (rest : List Nat) :
    parseRows n m rows.length (rows.flatMap rowWords ++ rest) = some (rows, rest) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [parseRows, List.append_assoc, ih]

def tableWords (table : Table) : List Nat :=
  [table.vertices, table.darts] ++ (rowList table).flatMap rowWords

def tableBits (table : Table) : List Bool := encodeWords (tableWords table)

def decodeTableWords : List Nat → Option Table
  | vertices :: darts :: words => do
      let (parsed, trailing) ← parseRows vertices darts darts words
      if trailing = [] then
        if length_ok : parsed.length = darts then
          let rows : Rows vertices darts := ⟨parsed.toArray, by simpa using length_ok⟩
          if valid : Valid rows then some ⟨vertices, darts, rows, valid⟩ else none
        else none
      else none
  | _ => none

@[simp] theorem decodeTableWords_encoded (table : Table) :
    decodeTableWords (tableWords table) = some table := by
  cases table with
  | mk vertices darts rows valid =>
      have parsed := parseRows_encoded rows.toList []
      simp only [Vector.length_toList, List.append_nil] at parsed
      simp [tableWords, rowList, decodeTableWords, parsed, valid, Vector.toArray_toList]

def decodeTableBits (bits : List Bool) : Option Table :=
  decodeWords bits >>= decodeTableWords

@[simp] theorem decodeTableBits_encoded (table : Table) :
    decodeTableBits (tableBits table) = some table := by
  simp [decodeTableBits, tableBits]

def encoding : Computability.Encoding Table Bool where
  encode := tableBits
  decode := decodeTableBits
  decode_encode := decodeTableBits_encoded

theorem tableBits_injective : Function.Injective tableBits := encoding.encode_injective

@[simp] theorem rowWords_length {n m : Nat} (row : DartRow n m) :
    (rowWords row).length = 4098 := by simp [rowWords]

theorem rowsWords_length {n m : Nat} (rows : List (DartRow n m)) :
    (rows.flatMap rowWords).length = 4098 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [ih, Nat.mul_add, Nat.add_comm]

@[simp] theorem tableWords_length (table : Table) :
    (tableWords table).length = 2 + 4098 * table.darts := by
  simp only [tableWords, List.length_append, List.length_cons, List.length_nil,
    rowsWords_length, rowList_length]

theorem tableWords_length_le_bits (table : Table) :
    2 + 4098 * table.darts ≤ (tableBits table).length := by
  rw [tableBits, encodeWords_length, ← tableWords_length]
  omega

theorem relationBits_length_le (relation : RelationTable) :
    (encodeWords (relationWords relation)).length ≤ 8192 := by
  have h := encodeWords_length_le (relationWords relation) 1 (by
    intro word hword
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp hword
    cases bit <;> decide)
  simpa only [relationWords_length] using h

theorem rowBits_length_le {n m : Nat} (row : DartRow n m) :
    (encodeWords (rowWords row)).length ≤ n + m + 8192 := by
  have ht := row.tail.isLt
  have hr := row.reverseIndex.isLt
  have hp := relationBits_length_le row.relation
  simp only [rowWords, encodeWords_append, List.length_append, encodeWords,
    encodeWord_length, List.length_nil] at ⊢
  omega

theorem rowsBits_length_le {n m : Nat} (rows : List (DartRow n m)) :
    (encodeWords (rows.flatMap rowWords)).length ≤ rows.length * (n + m + 8192) := by
  induction rows with
  | nil => simp [encodeWords]
  | cons row rows ih =>
      have hrow := rowBits_length_le row
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem tableBits_length_le (table : Table) :
    (tableBits table).length ≤ table.vertices + table.darts + 2 +
      table.darts * (table.vertices + table.darts + 8192) := by
  have hrows := rowsBits_length_le (rowList table)
  rw [rowList_length] at hrows
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem vertices_le_tableBits_length (table : Table) :
    table.vertices ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem darts_le_tableBits_length (table : Table) :
    table.darts ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end IndependentSetsGames.Foundations.PCP.GraphTables

end OAI
