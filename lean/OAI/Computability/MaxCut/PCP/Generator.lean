import Mathlib
import OAI.Computability.MaxCut.Machines.RuntimeSpace
import OAI.Computability.MaxCut.PCP.Gap

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceGenerator

open Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram SourceGeneratorContract

noncomputable section

variable {u D : Nat}
local instance : DecidableEq (Extra u D) := Classical.decEq _

def prefixPolynomial (u D : Nat) : Polynomial Nat :=
  SourceStartup.timePolynomial u D + SourceGeneratorTraversal.timePolynomial u D + 1

def timePolynomial (u D : Nat) (hD : 0 < D) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (SourceGeneratorProgram.machine u D hD)
    (clearKeys u D).length (prefixPolynomial u D)

def beforeFinish (F : Formula) (hD : 0 < D) : (SourceGeneratorProgram.machine u D hD).Cfg :=
  ⟨SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish,
    (initialAmbient u D hD, none), SourceGeneratorTraversal.traversalOutput F hD⟩

def enterFinishInTime (F : Formula) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      ⟨some .finishEnter, (initialAmbient u D hD, none),
        SourceGeneratorTraversal.traversalOutput F hD⟩
      (some (beforeFinish F hD)) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux
      (Reduction.MachineTransfer.exitAt (accumulatorTape u D)
        (SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish))
      _ _) = _
    cases h : SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish <;>
      simp only [Reduction.MachineTransfer.exitAt, beforeFinish, TM2.stepAux] <;>
      erw [h] <;> rfl
  steps_le_m := Nat.le_refl _

def prefixInTime (F : Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      (initList (SourceGeneratorProgram.machine u D hD) (formulaBits F))
      (some (beforeFinish F hD)) ((prefixPolynomial u D).eval (formulaBits F).length) := by
  have start := startupInTime (u := u) F hm hD
  let traversal := Classical.choice (SourceGeneratorTraversal.traversalInPolynomialTime
    (u := u) F hm hD)
  have first := StateTransition.EvalsToInTime.trans
    (SourceGeneratorProgram.machine u D hD).step _ _ _ _ _ start traversal
  have joined := StateTransition.EvalsToInTime.trans
    (SourceGeneratorProgram.machine u D hD).step _ _ _ _ _ first (enterFinishInTime F hD)
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply joined.steps_le_m.trans
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_one]
  omega

theorem output_empty (F : Formula) (hD : 0 < D) :
    SourceGeneratorTraversal.traversalOutput F hD (outputTape u D) = [] := by
  rw [SourceGeneratorTraversal.traversalOutput_frame F hD _
    (Ne.symm (accumulator_ne_output u D))]
  exact SourceStartup.ready_work_blank F (.extra (.inr ()))
    (by simp) (by simp) (by simp)

theorem halted_configuration (F : Formula) (hD : 0 < D) :
    (⟨none, (initialAmbient u D hD, none),
      SourceRuntimeFinish.canonicalTapes (outputTape u D)
        (SourceGeneratorTraversal.traversalOutput F hD (accumulatorTape u D)).reverse⟩ :
      (SourceGeneratorProgram.machine u D hD).Cfg) =
      haltList (SourceGeneratorProgram.machine u D hD)
        (MaxCutGames.Reduction.SourceEncoding.inputBits (SourceOccurrences.sourceInput F u D hD)) := by
  rw [SourceGeneratorTraversal.traversalOutput_accumulator, List.reverse_reverse]
  simp only [haltList, SourceGeneratorProgram.machine]
  congr 1
  funext k
  by_cases hk : k = outputTape u D
  · subst k
    simp [SourceRuntimeFinish.canonicalTapes]
    erw [Function.update_self]
    rfl
  · simp [SourceRuntimeFinish.canonicalTapes, hk]
    erw [Function.update_of_ne hk]

def outputInTime (F : NonemptyFormula) (hD : 0 < D) :
    TM2OutputsInTime (SourceGeneratorProgram.machine u D hD) (inputEncoding F)
      (some (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)))
      ((timePolynomial u D hD).eval (inputEncoding F).length) := by
  have hm : 0 < F.val.clauses.length := List.length_pos_iff.mpr F.property
  have prefixRun := prefixInTime (u := u) F.val hm hD
  have keepAcc : accumulatorTape u D ∉ clearKeys u D := by
    simp [mem_clearKeys]
  have keepOut : outputTape u D ∉ clearKeys u D := by
    simp [mem_clearKeys]
  have covers : ∀ k, k ≠ accumulatorTape u D → k ≠ outputTape u D → k ∈ clearKeys u D :=
    fun k ha ho => (mem_clearKeys u D k).mpr ⟨ha, ho⟩
  have finish := SourceRuntimeFinish.finishInTime (clearKeys u D)
    (accumulatorTape u D) (outputTape u D) (accumulator_ne_output u D)
    keepAcc keepOut covers (initialAmbient u D hD) SourceGeneratorProgram.Label.finish none
    (SourceGeneratorProgram.program u D hD) (fun _ => rfl)
    (SourceGeneratorTraversal.traversalOutput F.val hD) (output_empty F.val hD)
    (initialAmbient u D hD) none
  erw [halted_configuration F.val hD] at finish
  have joined := SourceRuntimeSpace.prefixAndFinishInTime
    (SourceGeneratorProgram.machine u D hD) (formulaBits F.val) (prefixPolynomial u D)
    prefixRun (clearKeys u D) (accumulatorTape u D) (outputTape u D)
    keepAcc keepOut covers (SourceGeneratorTraversal.traversalOutput F.val hD)
    (output_empty F.val hD) (fun _ => rfl) finish
  exact joined

def computableInPolyTime (u D : Nat) (hD : 0 < D) :
    TM2ComputableInPolyTime inputEncoding MaxCutGames.Reduction.SourceEncoding.inputBits
      (sourceMap u D hD) where
  tm := SourceGeneratorProgram.machine u D hD
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial u D hD
  outputsFun F := by
    change TM2OutputsInTime (machine u D hD) ((inputEncoding F).map id)
      (some ((MaxCutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)).map id)) _
    have hi := @List.map_id ((machine u D hD).Γ (machine u D hD).k₀) (inputEncoding F)
    have ho := @List.map_id ((machine u D hD).Γ (machine u D hD).k₁)
      (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F))
    simpa only [hi, ho] using outputInTime (u := u) F hD

theorem finite_work_alphabets (u D : Nat) (hD : 0 < D)
    (k : (computableInPolyTime u D hD).tm.K) :
    Finite ((computableInPolyTime u D hD).tm.Γ k) := by
  change Finite Bool
  infer_instance

def forErrorComputableInPolyTime (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    TM2ComputableInPolyTime inputEncoding MaxCutGames.Reduction.SourceEncoding.inputBits
      (errorMap η ξ hη hη1 hξ) := by
  let D := SourceNoiseParameter.noiseDenominator ξ
  let hD := SourceNoiseParameter.noiseDenominator_pos ξ
  let u := SourceGap.repetitionCount η ξ hη hη1 hξ D hD
  exact computableInPolyTime u D hD

theorem forError_finite_work_alphabets (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (k : (forErrorComputableInPolyTime η ξ hη hη1 hξ).tm.K) :
    Finite ((forErrorComputableInPolyTime η ξ hη hη1 hξ).tm.Γ k) := by
  change Finite Bool
  infer_instance

end

end MaxCutGames.Foundations.Hastad.SourceGenerator

namespace MaxCutGames.Foundations.PCP

structure ConstraintGraph (V E A : Type*) where
  reverse : E ≃ E
  reverse_involutive : Function.Involutive reverse
  tail : E → V
  accepts : E → A → A → Bool
  reverse_accepts : ∀ e a b, accepts (reverse e) b a = accepts e a b

namespace ConstraintGraph

variable {V E A : Type*}

def head (G : ConstraintGraph V E A) (e : E) : V := G.tail (G.reverse e)

@[simp] theorem head_reverse (G : ConstraintGraph V E A) (e : E) :
    G.head (G.reverse e) = G.tail e := by
  simp only [head, G.reverse_involutive e]

def edgeSatisfied (G : ConstraintGraph V E A) (labeling : V → A) (e : E) : Bool :=
  G.accepts e (labeling (G.tail e)) (labeling (G.head e))

@[simp] theorem edgeSatisfied_reverse (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    G.edgeSatisfied labeling (G.reverse e) = G.edgeSatisfied labeling e := by
  simpa only [edgeSatisfied, head, G.reverse_involutive e] using
    G.reverse_accepts e (labeling (G.tail e)) (labeling (G.tail (G.reverse e)))

def Satisfiable (G : ConstraintGraph V E A) : Prop :=
  ∃ labeling : V → A, ∀ e, G.edgeSatisfied labeling e = true

def rejectedDarts [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) :
    Finset E := Finset.univ.filter (fun e => G.edgeSatisfied labeling e = false)

def rejectionCount [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) : Nat :=
  (G.rejectedDarts labeling).card

theorem mem_rejectedDarts [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    e ∈ G.rejectedDarts labeling ↔ G.edgeSatisfied labeling e = false := by
  simp [rejectedDarts]

theorem rejectionCount_le [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) : G.rejectionCount labeling ≤ Fintype.card E := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem rejected_exists_of_not_satisfiable (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    ∃ e, G.edgeSatisfied labeling e = false := by
  classical
  by_contra none
  apply unsat
  refine ⟨labeling, fun e => ?_⟩
  have notFalse : G.edgeSatisfied labeling e ≠ false := by
    intro h
    exact none ⟨e, h⟩
  cases h : G.edgeSatisfied labeling e <;> simp_all

theorem rejectionCount_positive [Fintype E] (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    1 ≤ G.rejectionCount labeling := by
  obtain ⟨e, he⟩ := G.rejected_exists_of_not_satisfiable unsat labeling
  exact Finset.one_le_card.mpr ⟨e, (G.mem_rejectedDarts labeling e).mpr he⟩

end ConstraintGraph

end MaxCutGames.Foundations.PCP

/-!
# Executable directed-dart tables for the fixed 64-label alphabet

The header gives vertex and dart counts. Every dart has one ordered row:
tail index, reverse-dart index, and 4096 Boolean predicate entries. Entry
`b + 64 * a` is the predicate at labels `(a,b)`. All fields, including bits
as 0/1 words, use the existing zero-delimited unary natural-word codec.

The decoder checks all index bounds, row counts, predicate lengths, reverse
involution, predicate transpose, and absence of trailing fields. Directed rows
preserve loops, self-reversing darts, and repeated constraint occurrences.
The size theorems concern the full encoded table, not a machine runtime.
-/

namespace MaxCutGames.Foundations.PCP.GraphTables

open MaxCutGames.Foundations.Complexity

abbrev Label := Fin 64
abbrev RelationTable := Vector Bool 4096

/-- The fixed row-major ordering of the complete predicate table. -/
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

/-- The row itself is finite data; index bounds are checked while parsing. -/
structure DartRow (vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : RelationTable

abbrev Rows (vertices darts : Nat) := Vector (DartRow vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows n m) (e : Fin m) (a b : Label) : Bool :=
  relationAt rows[e].relation a b

/-- The two graph laws are decidable finite checks on the stored rows. -/
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

/-- The ordered list serialized by the codec. Equal rows remain separate. -/
def rowList (table : Table) : List (DartRow table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : Table) : (rowList table).length = table.darts := by
  simp [rowList]

/-- Decode validated finite data into the actual constraint-graph semantics. -/
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

private theorem constraintGraph_ext_inline_GraphTables {V E A : Type*} {G H : ConstraintGraph V E A}
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
    (G : ConstraintGraph (Fin n) (Fin m) Label) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext_inline_GraphTables
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

/-- Explicit enumerations determine every vertex name, dart position, and
predicate label. No hidden choice of a graph representation is made. -/
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

/-- Every directed occurrence contributes once before and after enumeration. -/
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

/-- A concrete encoding suitable for the existing TM2 computation interface. -/
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

/-- At least one unary delimiter is stored for every field, including all
4096 entries of every predicate table. -/
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

/-- Full unary size bound: headers, both bounded indices in every row, and
every Boolean predicate entry are counted. This is not a runtime assertion. -/
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

end MaxCutGames.Foundations.PCP.GraphTables

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

namespace MaxCutGames.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

theorem walkEnd_append (G : PortGraph V D) (v : V) (as bs : List D) :
    walkEnd G v (as ++ bs) = walkEnd G (walkEnd G v as) bs := by
  induction as generalizing v with
  | nil => rfl
  | cons d ds ih => exact ih (next G v d)

/-- Exposes the first dart and the independent remaining port word. -/
def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

/-- Advance across the first edge while retaining its reverse port. -/
def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

/-- Relabeling time coordinates is a bijection on actual port words. -/
def permutePorts {t : Nat} (σ : Fin t ≃ Fin t) : Walk V D t ≃ Walk V D t where
  toFun w := (w.1, fun j => w.2 (σ j))
  invFun w := (w.1, fun j => w.2 (σ.symm j))
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact congrArg w.2 (σ.apply_symm_apply j)
  right_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact congrArg w.2 (σ.symm_apply_apply j)

def wordEnd (G : PortGraph V D) : (n : Nat) → V → (Fin n → D) → V
  | 0, v, _ => v
  | n + 1, v, p => wordEnd G n (next G v (p 0)) (fun j => p j.succ)

def endpoint (G : PortGraph V D) {n : Nat} (w : Walk V D n) : V :=
  wordEnd G n w.1 w.2

theorem natCard_walk [Finite V] [Finite D] (n : Nat) :
    Nat.card (Walk V D n) = Nat.card V * Nat.card D ^ n := by
  simp [Walk, Nat.card_prod, Nat.card_fun]

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def advanceTail {n : Nat} (G : PortGraph V D) (w : Walk V D (n + 1)) : Walk V D n :=
  ((G.rot (w.1, w.2 0)).1, fun j => w.2 j.succ)

/-- The dart at the indicated time, computed by the actual preceding steps. -/
def edgeAt (G : PortGraph V D) :
    (n : Nat) → Walk V D (n + 1) → Fin (n + 1) → Edge V D
  | 0, w, _ => (w.1, w.2 0)
  | n + 1, w, k => Fin.cases (w.1, w.2 0)
      (fun j => edgeAt G n (advanceTail G w) j) k

/-- Isolate any actual path edge. Previously traversed ports are replaced by
their arrival ports, so the change of coordinates remains invertible. -/
def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

theorem pivotEquiv_fst (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      (pivotEquiv G n k w).1 = edgeAt G n w k := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change (pivotEquiv G n j (advanceTail G w)).1 =
        edgeAt G n (advanceTail G w) j
      exact ih j (advanceTail G w)

theorem edgeAt_port (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      (edgeAt G n w k).2 = w.2 k := by
  intro n
  induction n with
  | zero =>
    intro w k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · exact ih (advanceTail G w) j

theorem pivotEquiv_zero_apply (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    pivotEquiv G n 0 w = ((w.1, w.2 0), fun j => w.2 j.succ) := by
  cases n <;> rfl

theorem pivotEquiv_succ_apply (G : PortGraph V D)
    (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 2)) :
    pivotEquiv G (n + 1) k.succ w =
      ((pivotEquiv G n k (advanceTail G w)).1,
       Fin.cases (G.rot (w.1, w.2 0)).2
         (pivotEquiv G n k (advanceTail G w)).2) := rfl

def projectedFiberEquiv {X E R : Type*} (e : X ≃ E × R) (f : X → E)
    (he : ∀ x, (e x).1 = f x) (a : E) : {x // f x = a} ≃ R where
  toFun x := (e x.val).2
  invFun r := ⟨e.symm (a, r), by
    exact (he _).symm.trans (congrArg Prod.fst (e.apply_symm_apply (a, r)))⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext ((he x.val).trans x.property).symm rfl
  right_inv r := congrArg Prod.snd (e.apply_symm_apply (a, r))

def projectedEventEquiv {X E R : Type*} (e : X ≃ E × R) (f : X → E)
    (he : ∀ x, (e x).1 = f x) (P : E → Prop) :
    {x // P (f x)} ≃ ({a // P a} × R) where
  toFun x := (⟨(e x.val).1, by rw [he]; exact x.property⟩, (e x.val).2)
  invFun ar := ⟨e.symm (ar.1.val, ar.2), by
    have h : f (e.symm (ar.1.val, ar.2)) = ar.1.val :=
      (he _).symm.trans (congrArg Prod.fst (e.apply_symm_apply (ar.1.val, ar.2)))
    simpa only [h] using ar.1.property⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  right_inv ar := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.apply_symm_apply (ar.1.val, ar.2))
    · change (e (e.symm (ar.1.val, ar.2))).2 = ar.2
      exact congrArg Prod.snd (e.apply_symm_apply (ar.1.val, ar.2))

/-- Every fixed dart has exactly the same number of path realizations. -/
theorem natCard_edgeAt_fiber (G : PortGraph V D) (n : Nat) (k : Fin (n + 1))
    (a : Edge V D) :
    Nat.card {w : Walk V D (n + 1) // edgeAt G n w k = a} = Nat.card D ^ n := by
  calc
    _ = Nat.card (Fin n → D) := Nat.card_congr
      (projectedFiberEquiv (pivotEquiv G n k) (fun w => edgeAt G n w k)
        (pivotEquiv_fst G n k) a)
    _ = _ := by simp [Nat.card_fun]

/-- The exact event count underlying the uniform-pivot probability law. -/
theorem natCard_edgeAt_event (G : PortGraph V D) (n : Nat) (k : Fin (n + 1))
    (P : Edge V D → Prop) :
    Nat.card {w : Walk V D (n + 1) // P (edgeAt G n w k)} =
      Nat.card {a : Edge V D // P a} * Nat.card D ^ n := by
  calc
    _ = Nat.card ({a : Edge V D // P a} × (Fin n → D)) := Nat.card_congr
      (projectedEventEquiv (pivotEquiv G n k) (fun w => edgeAt G n w k)
        (pivotEquiv_fst G n k) P)
    _ = _ := by simp [Nat.card_prod, Nat.card_fun]

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

theorem leftFromPivot_zero (G : PortGraph V D) (n : Nat)
    (v : V) (r : Fin n → D) : leftFromPivot G n 0 v r = v := by
  cases n <;> rfl

theorem rightFromPivot_zero (G : PortGraph V D) (n : Nat)
    (e : Edge V D) (r : Fin n → D) :
    rightFromPivot G n 0 e r = wordEnd G n (next G e.1 e.2) r := by
  cases n <;> rfl

theorem leftFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      leftFromPivot G n k (pivotEquiv G n k w).1.1 (pivotEquiv G n k w).2 = w.1 := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change next G
        (leftFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1.1
          (pivotEquiv G n j (advanceTail G w)).2)
        (G.rot (w.1, w.2 0)).2 = w.1
      rw [ih j (advanceTail G w)]
      change (G.rot ((G.rot (w.1, w.2 0)).1, (G.rot (w.1, w.2 0)).2)).1 = w.1
      exact congrArg Prod.fst (rot_rot G (w.1, w.2 0))

theorem rightFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      rightFromPivot G n k (pivotEquiv G n k w).1 (pivotEquiv G n k w).2 =
        endpoint G w := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change rightFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1
        (pivotEquiv G n j (advanceTail G w)).2 = endpoint G w
      rw [ih j (advanceTail G w)]
      rfl

end MaxCutGames.Foundations.PCP.PoweringWalks

end OAI
