import Mathlib
import OAI.Computability.MaxCut.PCP.PoweringDecoding

namespace OAI

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

namespace MaxCutGames.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

private theorem match_in_tail_inline_PoweringOpinionTables (p : X → Prop) {a : X} {xs : List X}
    (h : ∃ b ∈ a :: xs, p b) (ha : ¬p a) : ∃ b ∈ xs, p b := by
  obtain ⟨b, hb, hp⟩ := h
  rcases List.mem_cons.mp hb with he | hm
  · exact False.elim (ha (he ▸ hp))
  · exact ⟨b, hm, hp⟩

def firstIndex (p : X → Prop) [DecidablePred p] :
    (xs : List X) → (∃ a ∈ xs, p a) → Fin xs.length
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨0, Nat.zero_lt_succ xs.length⟩ else
      (firstIndex p xs (match_in_tail_inline_PoweringOpinionTables p h ha)).succ

/-- The stored index selects the very same first address as `scanWitness`,
not just an address with the same endpoint. -/
theorem get_firstIndex (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a),
      xs.get (firstIndex p xs h) = (scanWitness p xs h).val := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h
    by_cases ha : p a
    · simp [firstIndex, scanWitness, ha]
    · simpa only [firstIndex, scanWitness, ha, dite_false, List.get_cons_succ'] using
        ih (match_in_tail_inline_PoweringOpinionTables p h ha)

theorem firstIndex_matches (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) : p (xs.get (firstIndex p xs h)) := by
  rw [get_firstIndex]
  exact (scanWitness p xs h).property

/-- Every earlier stored address fails the matching predicate. -/
theorem firstIndex_is_first (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a) (j : Fin xs.length),
      j.val < (firstIndex p xs h).val → ¬p (xs.get j) := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h j
    by_cases ha : p a
    · simp [firstIndex, ha]
    · refine Fin.cases (by intro _; exact ha) (fun i => ?_) j
      intro hi
      apply ih (match_in_tail_inline_PoweringOpinionTables p h ha) i
      exact Nat.lt_of_succ_lt_succ (by
        simpa only [firstIndex, ha, dite_false, Fin.val_succ] using hi)

/-- A local label slot is an index into the explicit bounded address list. -/
abbrev AddressIndex (d t : Nat) := Fin (allAddresses d t).length

variable {vertices d : Nat}

def addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) : AddressIndex d t :=
  firstIndex (fun w => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

theorem addressIndex_get (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (allAddresses d t).get (addressIndex G t center u) =
      (finitePortSelector G t center).address u := by
  change (allAddresses d t).get (firstIndex
    (fun w => (wordToBall G t center w).val = u.val) (allAddresses d t) _) =
      (scanWitness _ _ _).val
  exact get_firstIndex _ _ _

theorem addressIndex_matches (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    wordToBall G t center ((allAddresses d t).get (addressIndex G t center u)) = u := by
  rw [addressIndex_get]
  exact (finitePortSelector G t center).correct u

theorem addressIndex_is_first (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (j : AddressIndex d t)
    (hj : j.val < (addressIndex G t center u).val) :
    (wordToBall G t center ((allAddresses d t).get j)).val ≠ u.val := by
  exact firstIndex_is_first _ _ _ j hj

/-- The address bound depends on degree and radius, not the vertex count. -/
theorem addressIndex_lt (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (addressIndex G t center u).val < ∑ n : Fin (t + 1), d ^ n.val := by
  rw [← length_allAddresses]
  exact (addressIndex G t center u).isLt

abbrev LabelTable (d t : Nat) (A : Type*) := Vector A (allAddresses d t).length

/-- Materialize a padded label in the common address order. -/
def labelTable {t : Nat} (a : PaddedLabel (Fin d) t A) : LabelTable d t A :=
  Vector.ofFn fun i => a ((allAddresses d t).get i)

@[simp] theorem labelTable_get {t : Nat} (a : PaddedLabel (Fin d) t A)
    (i : AddressIndex d t) :
    (labelTable a)[i] = a ((allAddresses d t).get i) := by
  simp [labelTable]

/-- Exact evaluation bridge for every local target, with no consistency
assumption on labels at distinct addresses that reach the same vertex. -/
theorem labelTable_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (a : PaddedLabel (Fin d) t A) :
    (labelTable a)[addressIndex G t center u] =
      decode (finitePortSelector G t center) a u := by
  rw [labelTable_get, addressIndex_get]
  rfl

/-- One finite row for each constraint checked along a recorded walk. -/
structure WalkOpinionRow (vertices d t : Nat) where
  edge : Edge (Fin vertices) (Fin d)
  tailIndex : AddressIndex d t
  headIndex : AddressIndex d t

abbrev WalkRows (vertices d n : Nat) := Vector (WalkOpinionRow vertices d (n + 1)) (n + 1)

/-- The only target vertices inspected are the actual edge endpoints. -/
def walkRows (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : WalkRows vertices d n :=
  Vector.ofFn fun k =>
    { edge := edgeAt G n w k
      tailIndex := addressIndex G (n + 1) w.1 (tailFromStart G n w k)
      headIndex := addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) }

@[simp] theorem walkRows_edge (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    (walkRows G n w)[k].edge = edgeAt G n w k := by
  simp [walkRows]

@[simp] theorem walkRows_tail_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable a)[(walkRows G n w)[k].tailIndex] =
      decode (finitePortSelector G (n + 1) w.1) a (tailFromStart G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) w.1 (tailFromStart G n w k) a

@[simp] theorem walkRows_head_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (b : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable b)[(walkRows G n w)[k].headIndex] =
      decode (finitePortSelector G (n + 1) (endpoint G w)) b (headFromEnd G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) b

theorem walkRows_length (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    (walkRows G n w).toList.length = n + 1 := by
  simp

/-- Evaluate an already stored row vector by finite label lookups. The only
quantified type is the bounded set of walk positions. -/
def rowsAccepts {n : Nat} (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool)
    (rows : WalkRows vertices d n) (a b : LabelTable d (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1), accepts rows[k].edge a[rows[k].tailIndex]
    b[rows[k].headIndex] = true)

/-- The stored finite lookup predicate implements the actual powering test. -/
theorem rowsAccepts_walkRows (G : PortGraph (Fin vertices) (Fin d))
    (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : PaddedLabel (Fin d) (n + 1) A) :
    rowsAccepts accepts (walkRows G n w) (labelTable a) (labelTable b) =
      PoweringTest.pathAccepts G accepts n (finitePortSelector G (n + 1)) w a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowsAccepts, decide_eq_true_iff, PoweringTest.pathAccepts_eq_true_iff,
    walkRows_edge, walkRows_tail_value, walkRows_head_value]

end MaxCutGames.Foundations.PCP.PoweringOpinionTables

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

namespace MaxCutGames.Foundations.PCP.GenericGraphTables

open MaxCutGames.Foundations.Complexity

abbrev Label (q : Nat) := Fin q
abbrev RelationTable (q : Nat) := Vector Bool (q * q)

variable {q : Nat}

/-- The fixed row-major ordering of the complete predicate table. -/
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

/-- The row itself is finite data; index bounds are checked while parsing. -/
structure DartRow (q vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : (RelationTable q)

abbrev Rows (q vertices darts : Nat) := Vector (DartRow q vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows q n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows q n m) (e : Fin m) (a b : (Label q)) : Bool :=
  relationAt rows[e].relation a b

/-- The two graph laws are decidable finite checks on the stored rows. -/
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

/-- The ordered list serialized by the codec. Equal rows remain separate. -/
def rowList (table : (Table q)) : List (DartRow q table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : (Table q)) : (rowList table).length = table.darts := by
  simp [rowList]

/-- Decode validated finite data into the actual constraint-graph semantics. -/
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

private theorem constraintGraph_ext_inline_GenericGraphTables {V E A : Type*} {G H : ConstraintGraph V E A}
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

/-- Complete semantic graph roundtrip, including its actual reversal map. -/
@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext_inline_GenericGraphTables
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

/-- Explicit enumerations determine every vertex name, dart position, and
predicate label. No hidden choice of a graph representation is made. -/
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

/-- Every directed occurrence contributes once before and after enumeration. -/
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

/-- A concrete encoding for the fixed alphabet, suitable for the existing TM2 computation interface. -/
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

/-- At least one unary delimiter is stored for every field, including all
(q * q) entries of every predicate table. -/
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

/-- Full unary size bound: headers, both bounded indices in every row, and
every Boolean predicate entry are counted. This is not a runtime assertion. -/
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

end MaxCutGames.Foundations.PCP.GenericGraphTables

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

namespace MaxCutGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

/-- Program-constant output alphabet size for degree `d` and walk length `n+1`. -/
def labelCount (d n : Nat) : Nat := 64 ^ addressCount d (n + 1)

/-- Number of directed recorded-walk occurrences, including orientation. -/
def dartCount (vertices d n : Nat) : Nat := 2 * vertices * d ^ (n + 1)

def mathematicalGraph {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    ConstraintGraph (Fin vertices) (PoweringTest.Dart (Fin vertices) (Fin d) n)
      (PaddedLabel (Fin d) (n + 1) (Fin 64)) :=
  PoweringTest.poweredGraph (PortTables.portGraph input) (PortTables.accepts input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1))

/-- The finite first-address predicate evaluator used for each stored row. -/
def rowAccepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) : Bool :=
  let rows := PoweringOpinionTables.walkRows (PortTables.portGraph input) n e.2
  let left := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 a)
  let right := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 b)
  if e.1 then PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows right left
    else PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows left right

theorem rowAccepts_eq {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) :
    rowAccepts input n e a b = (mathematicalGraph input n).accepts e
      (decodeLabel d (n + 1) 64 a) (decodeLabel d (n + 1) 64 b) := by
  rcases e with ⟨direction, w⟩
  cases direction <;>
    simp only [rowAccepts, mathematicalGraph, PoweringTest.poweredGraph, Bool.false_eq_true,
      ite_false, ite_true, PoweringOpinionTables.rowsAccepts_walkRows]

def table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.Table (labelCount d n) :=
  GenericGraphTables.ofEnumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
    (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64)

@[simp] theorem table_vertices {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).vertices = vertices := rfl

@[simp] theorem table_darts {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).darts = dartCount vertices d n := rfl

/-- Complete decoded semantics, with executable vertex, dart and label orders. -/
theorem semantics_table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.semantics (table input n) =
      GenericGraphTables.enumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
        (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) :=
  GenericGraphTables.semantics_ofGraph _

/-- Each actual output relation entry is the bounded stored-opinion evaluator. -/
theorem table_accepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (i : Fin (dartCount vertices d n)) (a b : Fin (labelCount d n)) :
    GenericGraphTables.acceptsAt (table input n).rows i a b =
      rowAccepts input n (decodeDart vertices d n i) a b := by
  change (GenericGraphTables.semantics (table input n)).accepts i a b = _
  rw [semantics_table]
  exact (rowAccepts_eq input n (decodeDart vertices d n i) a b).symm

/-- The reverse row flips just the orientation in the recorded-walk encoding. -/
theorem table_reverse {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (direction : Bool) (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    GenericGraphTables.reverseAt (table input n).rows (encodeDart vertices d n (direction, w)) =
      encodeDart vertices d n (!direction, w) := by
  change (GenericGraphTables.semantics (table input n)).reverse _ = _
  rw [semantics_table]
  change dartEquiv vertices d n ((mathematicalGraph input n).reverse
      ((dartEquiv vertices d n).symm (dartEquiv vertices d n (direction, w)))) =
    dartEquiv vertices d n (!direction, w)
  rw [(dartEquiv vertices d n).symm_apply_apply]
  rfl

/-- Serialized output in the shared generic graph codec. -/
def outputBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) : List Bool :=
  GenericGraphTables.tableBits (table input n)

/-- The actual function on variable-size regular input tables. -/
def transform (d n : Nat) (input : PortTables.Input d) : GenericGraphTables.Table (labelCount d n) :=
  table input.2 n

end MaxCutGames.Foundations.PCP.PoweringTables

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

namespace MaxCutGames.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

/-- An arbitrary constraint graph's rejection probability is its actual
rejected-dart cardinal ratio, including the empty-dart case. -/
theorem constraint_rejection_mean_eq_count [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A) :
    SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) =
      (H.rejectionCount labels : ℝ) / (Fintype.card E : ℝ) := by
  classical
  rw [SpectralReturn.mean_eq_sum_div_card]
  simp only [PoweringMoment.bit, ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  apply congrArg (fun x : ℝ => x / (Fintype.card E : ℝ))
  convert (Finset.sum_boole (R := ℝ)
    (fun e => H.edgeSatisfied labels e = false) Finset.univ) using 1 ; try rfl
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : H.edgeSatisfied labels e = false <;> simp [h]

/-- Multiplying a normalized lower bound by the actual positive dart count. -/
theorem constraint_rejection_lower_iff [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A)
    (hcard : 0 < Fintype.card E) (ε : ℝ) :
    ε ≤ SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) ↔
      ε * (Fintype.card E : ℝ) ≤ (H.rejectionCount labels : ℝ) := by
  rw [constraint_rejection_mean_eq_count]
  exact le_div_iff₀ (Nat.cast_pos.mpr hcard)

/-- The edge-profile definition equals its actual directed-edge indicator
mean without any nonemptiness assumption on vertices or ports. -/
theorem edgeDensity_eq_bit_mean [Fintype V] [Fintype D]
    (bad : Edge V D → Bool) :
    SpectralReturn.edgeDensity bad =
      SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit (bad e = true)) := by
  convert (SpectralReturn.mean_prod
    (fun e : Edge V D => PoweringMoment.bit (bad e = true))).symm using 1 ; try rfl
  change SpectralReturn.mean (fun v => SpectralReturn.mean
    (fun d => if bad (v, d) then (1 : ℝ) else 0)) = _
  apply congrArg SpectralReturn.mean
  funext v
  apply congrArg SpectralReturn.mean
  funext d
  cases h : bad (v, d) <;> simp [PoweringMoment.bit]

/-- Decoded badness is exactly rejection in the actual base constraint graph. -/
theorem base_edgeDensity_eq_rejection_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) :
    SpectralReturn.edgeDensity (decodedBad G accepts assignment) =
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ) /
        (Fintype.card (Edge V D) : ℝ) := by
  calc
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        (decodedBad G accepts assignment e = true)) := edgeDensity_eq_bit_mean _
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        ((baseGraph G accepts reverse_accepts).edgeSatisfied assignment e = false)) := by
      apply congrArg SpectralReturn.mean
      funext e
      exact congrArg PoweringMoment.bit
        (propext (decodedBad_eq_true_iff G accepts assignment e))
    _ = _ := constraint_rejection_mean_eq_count _ _

theorem base_count_lower_to_density [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (hcard : 0 < Fintype.card (Edge V D)) (ε : ℝ)
    (hcount : ε * (Fintype.card (Edge V D) : ℝ) ≤
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ)) :
    ε ≤ SpectralReturn.edgeDensity (decodedBad G accepts assignment) := by
  rw [base_edgeDensity_eq_rejection_count G accepts reverse_accepts assignment]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).2 hcount

/-- The actual powered graph's directed-dart average is its rejected-dart
fraction. No nonemptiness premise is needed for this identity. -/
theorem powered_rejection_mean_eq_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) /
        (Fintype.card (Dart V D n) : ℝ) :=
  constraint_rejection_mean_eq_count _ _

/-- The recorded-walk rejection average used in soundness is the actual
powered graph's rejected-dart fraction. -/
theorem path_rejection_mean_eq_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
      (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) =
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) /
        (Fintype.card (Dart V D n) : ℝ) := by
  rw [← rejection_mean_eq_path_mean G accepts n selectors labels]
  exact powered_rejection_mean_eq_count G accepts n selectors labels

/-- Convert a proved path-test rejection lower bound into the actual powered
constraint graph's rejected-dart count inequality. -/
theorem powered_density_lower_to_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (hcard : 0 < Fintype.card (Dart V D n)) (ε : ℝ)
    (hlower : ε ≤ SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
      (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false))) :
    ε * (Fintype.card (Dart V D n) : ℝ) ≤
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) := by
  rw [path_rejection_mean_eq_count G accepts n selectors labels] at hlower
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).1 hlower

/-- Exact size of the powered dart type, retaining both direction flags and
all recorded port words, including repeated vertices and edges. -/
theorem natCard_dart [Finite V] [Finite D] (n : Nat) :
    Nat.card (Dart V D n) = 2 * Nat.card V * Nat.card D ^ (n + 1) := by
  simp [Dart, Walk, Nat.card_prod, Nat.card_fun, Nat.mul_assoc]

theorem fintypeCard_dart [Fintype V] [Fintype D] (n : Nat) :
    Fintype.card (Dart V D n) =
      2 * Fintype.card V * Fintype.card D ^ (n + 1) := by
  simpa only [Nat.card_eq_fintype_card] using (natCard_dart (V := V) (D := D) n)

/-- The common powered alphabet size depends only on degree, radius, and the
base alphabet. The ambient vertex cardinality does not occur. -/
theorem natCard_poweredAlphabet [Finite D] [Finite A] (n : Nat) :
    Nat.card (PaddedLabel D (n + 1) A) =
      Nat.card A ^ (∑ j : Fin (n + 2), Nat.card D ^ j.val) :=
  PoweringLabels.card_paddedLabel (n + 1)

/-- With finite numbered ports, the same exponent is the length of the
already constructed executable address enumeration. -/
theorem natCard_finitePortAlphabet [Finite A] (d n : Nat) :
    Nat.card (PaddedLabel (Fin d) (n + 1) A) =
      Nat.card A ^ (PoweringAddresses.allAddresses d (n + 1)).length := by
  rw [PoweringLabels.card_paddedLabel, PoweringAddresses.length_allAddresses]
  simp only [Nat.card_fin]

end MaxCutGames.Foundations.PCP.PoweringCounting

end OAI
