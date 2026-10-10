import OAI.Computability.PerfectCompleteness.Construction.CutNodeRows
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutCalls
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAgreementMean
import OAI.Computability.PerfectCompleteness.Foundations.OriginalWholeCutBridge

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutReconstruction

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

theorem cutSlots_append (p : Path branch n j) (r : Path branch j i)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    cutSlots (p.append r) slots = cutSlots r (cutSlots p slots) := by
  funext s a
  exact congrArg (fun leaf => slots leaf a) (p.slotEmbedding_append r s)

def cutSpaceEquiv (p : Path branch n j) (r : Path branch j i)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    H (cutSlots (p.append r) slots) ≃ H (cutSlots r (cutSlots p slots)) :=
  Equiv.cast (congrArg (fun s : Slots branch i → Fin t → MixedSupport.Slot => ↥(H s))
    (cutSlots_append p r slots))

abbrev FreshExterior (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalTerminalSplit.ExteriorTape F2 repeats r (LeafDomain (cutSlots p slots))

abbrev FreshValues (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  TerminalCalls.TerminalIndex repeats r → H (cutSlots (p.append r) slots)

abbrev FreshRecord (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  FreshValues repeats p r slots × FreshExterior repeats p r slots

def readFresh (repeats : Nat → Nat) (p : Path branch n j) (r : Path branch j i)
    (suffix : Path branch i k) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : RecursiveSampler.Tape F2 repeats (r.append suffix) (LeafDomain (cutSlots p slots))) :
    FreshRecord repeats p r slots :=
  let split := OriginalTerminalSplit.splitTape F2 repeats r suffix
    (LeafDomain (cutSlots p slots)) tape
  (fun call => (cutSpaceEquiv p r slots).symm
      (RecursiveSampler.evaluate F2 repeats suffix
        (r.family (LeafDomain (cutSlots p slots))) (split.1 call)), split.2)

def reconstructFresh (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : FreshRecord repeats p r slots) : H (cutSlots p slots) :=
  OriginalScalarReconstruction.reconstruct F2 repeats r (LeafDomain (cutSlots p slots))
    (fun call => cutSpaceEquiv p r slots (record.1 call)) record.2

theorem reconstructFresh_readFresh (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : RecursiveSampler.Tape F2 repeats (r.append suffix) (LeafDomain (cutSlots p slots))) :
    reconstructFresh repeats p r slots (readFresh repeats p r suffix slots tape) =
      RecursiveSampler.evaluate F2 repeats (r.append suffix) (LeafDomain (cutSlots p slots)) tape := by
  simpa only [reconstructFresh, readFresh, Equiv.apply_symm_apply] using
    OriginalScalarReconstruction.reconstruct_original F2 repeats r
      (LeafDomain (cutSlots p slots)) suffix tape

abbrev Exterior (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalWholeCutTape.Exterior rows repeats (p.append r) slots ×
    FreshExterior repeats p r slots

abbrev Record (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p r slots ×
    CutChildGrouping.Assembled (C := UpperScalarCutCalls.Index rows repeats p r)
      (cutSlots (p.append r) slots) rows

def pack (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (old : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (fresh : FreshRecord repeats p r slots) : Record rows repeats p r slots :=
  ((old.1, fresh.2), (Sum.elim old.2.1 fresh.1, old.2.2))

def oldRecord (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p r slots) :
    OriginalWholeCut.Record rows repeats (p.append r) slots :=
  (record.1.1, (fun call => record.2.1 (.inl call), record.2.2))

def freshRecord (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p r slots) : FreshRecord repeats p r slots :=
  (fun call => record.2.1 (.inr call), record.1.2)

def packEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalWholeCut.Record rows repeats (p.append r) slots × FreshRecord repeats p r slots) ≃
      Record rows repeats p r slots where
  toFun z := pack rows repeats p r slots z.1 z.2
  invFun z := (oldRecord rows repeats p r slots z, freshRecord rows repeats p r slots z)
  left_inv _ := rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext call
        cases call <;> rfl
      · rfl

def observe (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p r slots) :
    OriginalWholeCutBridge.NumberedRecord rows repeats (p.append r) slots × H (cutSlots p slots) :=
  (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots
      (oldRecord rows repeats p r slots record),
    reconstructFresh repeats p r slots (freshRecord rows repeats p r slots record))

def read (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    Record rows repeats p r slots :=
  pack rows repeats p r slots
    (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1)
    (readFresh repeats p r (.step chosen q) slots tapes.2)

theorem observe_read (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    observe rows repeats p r slots (read rows repeats p r chosen q slots tapes) =
      (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1),
      RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots)) tapes.2) := by
  apply Prod.ext
  · rfl
  · exact reconstructFresh_readFresh repeats p r (.step chosen q) slots tapes.2

def reconstruct (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p r slots) : Arrays slots rows × H (cutSlots p slots) :=
  (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots
      (oldRecord rows repeats p r slots record),
    reconstructFresh repeats p r slots (freshRecord rows repeats p r slots record))

theorem reconstruct_read (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    reconstruct rows repeats p r slots (read rows repeats p r chosen q slots tapes) =
      (WholeArraySampler.evaluate rows repeats ((p.append r).append (.step chosen q)) slots tapes.1,
      RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots)) tapes.2) := by
  apply Prod.ext
  · exact OriginalWholeCut.reconstruct_original rows repeats (p.append r) chosen q slots tapes.1
  · exact reconstructFresh_readFresh repeats p r (.step chosen q) slots tapes.2

abbrev NumberedRecord (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p r slots ×
    CutChildGrouping.Assembled
      (C := Fin (UpperScalarCutCalls.count rows repeats n j (i + 1)))
      (cutSlots (p.append r) slots) rows

def numberRecordEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Record rows repeats p r slots ≃ NumberedRecord rows repeats p r slots :=
  Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.arrowCongr (UpperScalarCutCalls.numbering rows repeats p r)
      (Equiv.refl _)) (Equiv.refl _))

def numberedObserve (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : NumberedRecord rows repeats p r slots) :
    OriginalWholeCutBridge.NumberedRecord rows repeats (p.append r) slots × H (cutSlots p slots) :=
  observe rows repeats p r slots ((numberRecordEquiv rows repeats p r slots).symm record)

@[simp] theorem numberedObserve_numberRecord (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (record : Record rows repeats p r slots) :
    numberedObserve rows repeats p r slots (numberRecordEquiv rows repeats p r slots record) =
      observe rows repeats p r slots record := by
  simp only [numberedObserve, Equiv.symm_apply_apply]

end
end PerfectCompleteness.UpperScalarCutReconstruction

end

section

namespace PerfectCompleteness.UpperScalarCutBucket

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

def descendRecord (rows repeats : Nat → Nat) :
    {n j i : Nat} → (p : Path branch n j) → (r : Path branch j (i + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        OriginalWholeCut.Record rows repeats (p.append r) slots →
          OriginalWholeCut.Record rows repeats r (cutSlots p slots)
  | _, _, _, .refl _, _, _, record => record
  | _, _, _, .step child p, r, slots, record =>
      descendRecord rows repeats p r (childSlots slots child)
        (record.1.2.1, (fun call => record.2.1 (.inr call), record.2.2))

theorem restrictArrays_reconstruct (rows repeats : Nat → Nat) (p : Path branch n j) :
    ∀ (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (record : OriginalWholeCut.Record rows repeats (p.append r) slots),
      WholeArraySubtreeSplit.restrictArrays rows p slots
          (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record) =
        OriginalWholeCut.reconstructRecord rows repeats r (cutSlots p slots)
          (descendRecord rows repeats p r slots record) := by
  induction p with
  | refl n =>
      intro r slots record
      cases r <;> rfl
  | step child p ih =>
      intro r slots record
      let lower : OriginalWholeCut.Record rows repeats (p.append r)
          (childSlots slots child) :=
        (record.1.2.1, (fun call => record.2.1 (.inr call), record.2.2))
      have hselected :
          (fun node => OriginalWholeCut.reconstructRecord rows repeats
            ((Path.step child p).append r) slots record (.inr (child, node))) =
            OriginalWholeCut.reconstructRecord rows repeats (p.append r)
              (childSlots slots child) lower := by
        funext node
        exact congrFun (WholeArraySampler.childrenAt_selected slots rows child
          (OriginalWholeCut.reconstructRecord rows repeats (p.append r)
            (childSlots slots child) lower) record.1.2.2) node
      exact (congrArg (WholeArraySubtreeSplit.restrictArrays rows p
        (childSlots slots child)) hselected).trans (ih r (childSlots slots child) lower)

def rootBuckets (rows repeats : Nat → Nat) :
    {j i : Nat} → (r : Path branch (j + 1) (i + 1)) →
      (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot) →
        OriginalWholeCut.Record rows repeats r slots →
          BucketSampler.Tape (rows (j + 1)) (H slots)
  | _, _, .refl _, _, record => record.2.1
  | _, _, .step child r, slots, record => fun direction =>
      OriginalScalarReconstruction.reconstruct F2 repeats (.step child r) (LeafDomain slots)
        (fun terminal => record.2.1 (.inl (direction, terminal))) (record.1.1 direction)

theorem rootRows_reconstruct (rows repeats : Nat → Nat)
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats r slots) :
    OriginalWholeCut.reconstructRecord rows repeats r slots record (.inl ()) =
      BucketSampler.evaluate (rows (j + 1)) (id : H slots → H slots)
        (rootBuckets rows repeats r slots record) := by
  cases r <;> rfl

def upperBuckets (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots) :
    BucketSampler.Tape (rows (j + 1)) (H (cutSlots p slots)) :=
  rootBuckets rows repeats r (cutSlots p slots) (descendRecord rows repeats p r slots record)

theorem selectedRows_reconstruct (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots) :
    SelectedArrayReplacement.selectedRows rows p slots
        (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record) =
      BucketSampler.evaluate (rows (j + 1)) (id : H (cutSlots p slots) → _)
        (upperBuckets rows repeats p r slots record) := by
  unfold SelectedArrayReplacement.selectedRows
  rw [restrictArrays_reconstruct]
  exact rootRows_reconstruct rows repeats r (cutSlots p slots) _

def descendTape (rows repeats : Nat → Nat) :
    {n j i k : Nat} → (p : Path branch n j) → (r : Path branch j (i + 1)) →
      (chosen : Fin (branch i)) → (q : Path branch i k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots →
          WholeArraySampler.Tape rows repeats (r.append (.step chosen q)) (cutSlots p slots)
  | _, _, _, _, .refl _, _, _, _, _, tape => tape
  | _, _, _, _, .step child p, r, chosen, q, slots, tape =>
      descendTape rows repeats p r chosen q (childSlots slots child)
        (tape (.inr (.inl ())))

theorem descendRecord_readRecord (rows repeats : Nat → Nat) (p : Path branch n j) :
    ∀ (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots),
      descendRecord rows repeats p r slots
          (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) =
        OriginalWholeCut.readRecord rows repeats r chosen q (cutSlots p slots)
          (descendTape rows repeats p r chosen q slots tape) := by
  induction p with
  | refl n =>
      intro r chosen q slots tape
      cases r <;> rfl
  | step child p ih =>
      intro r chosen q slots tape
      exact ih r chosen q (childSlots slots child) (tape (.inr (.inl ())))

def continuedRootTape (rows repeats : Nat → Nat) :
    {j i k : Nat} → (r : Path branch (j + 1) (i + 1)) →
      (chosen : Fin (branch i)) → (q : Path branch i k) →
      (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats (r.append (.step chosen q)) slots →
          WholeArraySampler.RootTape rows repeats (r.append (.step chosen q)) slots
  | _, _, _, .refl _, _, _, _, tape => tape (.inl ())
  | _, _, _, .step _ _, _, _, _, tape => tape (.inl ())

theorem rootBuckets_readRecord (rows repeats : Nat → Nat)
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (r.append (.step chosen q)) slots) :
    rootBuckets rows repeats r slots (OriginalWholeCut.readRecord rows repeats r chosen q slots tape) =
      fun direction => RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain slots) (continuedRootTape rows repeats r chosen q slots tape direction) := by
  cases r with
  | refl => rfl
  | step child r =>
      funext direction
      exact OriginalScalarReconstruction.reconstruct_original F2 repeats (.step child r)
        (LeafDomain slots) (.step chosen q) (tape (.inl ()) direction)

theorem upperBuckets_readRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots) :
    upperBuckets rows repeats p r slots
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) =
      fun direction => RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots))
        (continuedRootTape rows repeats r chosen q (cutSlots p slots)
          (descendTape rows repeats p r chosen q slots tape) direction) := by
  unfold upperBuckets
  rw [descendRecord_readRecord, rootBuckets_readRecord]

def replaceArrays (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    Arrays slots rows :=
  SelectedArrayReplacement.replace rows p slots
    (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record)
    (BucketSampler.evaluate (rows (j + 1)) (id : H (cutSlots p slots) → _)
      (Function.update (upperBuckets rows repeats p r slots record) a fresh))

theorem replaceArrays_rankOne (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    replaceArrays rows repeats p r slots record a fresh =
      SelectedArrayReplacement.replace rows p slots
        (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record)
        (SelectedArrayReplacement.selectedRows rows p slots
          (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record) +
            BucketSampler.rankOne a.val (fresh - upperBuckets rows repeats p r slots record a)) := by
  unfold replaceArrays
  rw [BucketSampler.evaluate_update, selectedRows_reconstruct]
  simp only [id_eq]

theorem replaceArrays_outside (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots))
    (node : Nodes branch n) (hnode : node ≠ upperNode p) :
    replaceArrays rows repeats p r slots record a fresh node =
      OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record node :=
  SelectedArrayReplacement.replace_outside rows p slots _ _ node hnode

theorem matrix_reconstruct (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots) :
    NodeEmbedding.matrix (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record)
        (upperNode p) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (CutNodeRows.bucketTapeEquiv rows p slots (upperBuckets rows repeats p r slots record)) := by
  rw [← CutNodeRows.matrixOfRows_selectedRows, selectedRows_reconstruct]
  exact CutNodeRows.matrixOfRows_evaluate rows p slots _

theorem matrix_replaceArrays (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    NodeEmbedding.matrix (replaceArrays rows repeats p r slots record a fresh) (upperNode p) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (Function.update
          (CutNodeRows.bucketTapeEquiv rows p slots (upperBuckets rows repeats p r slots record))
          (CutNodeRows.directionEquiv rows p a) (CutNodeRows.cutRowEquiv p slots fresh)) := by
  rw [← CutNodeRows.matrixOfRows_selectedRows]
  unfold replaceArrays
  rw [SelectedArrayReplacement.selectedRows_replace, CutNodeRows.matrixOfRows_evaluate,
    CutNodeRows.bucketTapeEquiv_update]

def pairRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p) :=
  (HierarchicalMatrixTable.backgroundOf slots (upperNode p)
      (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record),
    (NodeEmbedding.matrix (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record)
        (upperNode p),
      NodeEmbedding.matrix (replaceArrays rows repeats p r slots record a fresh) (upperNode p)))

theorem pairRecord_eq (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    pairRecord rows repeats p r slots record a fresh =
      HierarchicalAgreementMean.pairRecord slots (upperNode p)
        (HierarchicalMatrixTable.backgroundOf slots (upperNode p)
          (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record),
          CutNodeRows.bucketSampleEquiv rows p slots
            (a, (upperBuckets rows repeats p r slots record, fresh))) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact matrix_reconstruct rows repeats p r slots record
    · exact matrix_replaceArrays rows repeats p r slots record a fresh

def enlargedPairRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (j + 1)) ×
      UpperScalarCutReconstruction.Record rows repeats p r slots) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p) :=
  pairRecord rows repeats p r slots
    (UpperScalarCutReconstruction.oldRecord rows repeats p r slots sample.2) sample.1
    (UpperScalarCutReconstruction.reconstructFresh repeats p r slots
      (UpperScalarCutReconstruction.freshRecord rows repeats p r slots sample.2))

theorem enlargedPairRecord_read (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (a : BucketSampler.Direction (rows (j + 1)))
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    enlargedPairRecord rows repeats p r slots
        (a, UpperScalarCutReconstruction.read rows repeats p r chosen q slots tapes) =
      pairRecord rows repeats p r slots
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1) a
        (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)) tapes.2) := by
  change pairRecord rows repeats p r slots
    (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1) a
    (UpperScalarCutReconstruction.reconstructFresh repeats p r slots
      (UpperScalarCutReconstruction.readFresh repeats p r (.step chosen q) slots tapes.2)) = _
  rw [UpperScalarCutReconstruction.reconstructFresh_readFresh]

def numberedPairRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (j + 1)) ×
      UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p) :=
  enlargedPairRecord rows repeats p r slots
    (sample.1, (UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots).symm sample.2)

@[simp] theorem numberedPairRecord_numberRecord (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (a : BucketSampler.Direction (rows (j + 1)))
    (record : UpperScalarCutReconstruction.Record rows repeats p r slots) :
    numberedPairRecord rows repeats p r slots
        (a, UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots record) =
      enlargedPairRecord rows repeats p r slots (a, record) := by
  simp only [numberedPairRecord, Equiv.symm_apply_apply]

end
end PerfectCompleteness.UpperScalarCutBucket

end

end OAI
