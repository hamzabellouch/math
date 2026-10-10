import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ReaderInitializationMap
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationRecordInitialization

namespace OAI

/-! # Stored bounded-mask readers refine the original representation streams

The maps below are semantic views. Execution uses the bounded records and
shared backing array; reading preserves exactly the original cursor state.
-/

namespace LowSpaceSubsetSum.RepresentationStoredReader

variable {n : ℕ}

def sourceKey (D : RepresentationPairData n) :=
  FilteredStream.key D.wl D.wl D.modulus D.mode

def key (D : RepresentationPairData n) (x : LeafRecord n × LeafRecord n) : ℤ :=
  sourceKey D (RepresentationKeys.pairSemantic x)

private theorem recordKey_eq (D : RepresentationPairData n) :
    FilteredStream.key (fun x : LeafRecord n => D.wl x.semantic)
      (fun x : LeafRecord n => D.wl x.semantic) D.modulus D.mode = key D := by
  funext x
  dsimp only [key, sourceKey, RepresentationKeys.pairSemantic]
  cases D.mode <;> rfl

abbrev Cursor (D : RepresentationPairData n) :=
  FilteredStream.Cursor (α := LeafRecord n) D.rightRecords

def cursorMap (D : RepresentationPairData n) : Cursor D →
    FilteredStream.Cursor (α := RepresentationPairData.Occ (n := n))
      (D.rightRecords.map LeafRecord.semantic) :=
  FilteredStream.mapCursor LeafRecord.semantic LeafRecord.semantic D.rightRecords

abbrev State (D : RepresentationPairData n) :=
  MergedReader.State (key D) (FilteredStream.view (α := LeafRecord n) D.rightRecords)
    (Nat.clog 2 D.leftArray.size)

private theorem primary (D : RepresentationPairData n) :
    FilteredRow.PrimarySorted D.rightRecords (fun x => D.wl x.semantic) D.lowModulus :=
  ResidueSort.primary D.rawRightRecords _ _ _

private theorem secondary (D : RepresentationPairData n) :
    FilteredRow.SecondarySorted D.rightRecords (fun x => D.wl x.semantic)
      D.lowModulus D.modulus := ResidueSort.secondary D.rawRightRecords _ _ _

def rows (D : RepresentationPairData n) :
    RowMerge.Path (Nat.clog 2 D.leftArray.size) → Cursor D :=
  PaddedRows.rows (FilteredStream.rowArray D.leftRecords D.rightRecords
    (fun x => D.wl x.semantic) (fun x => D.wl x.semantic) D.lowModulus D.modulus
    D.residue (primary D) D.mode) _

private theorem rows_sorted (D : RepresentationPairData n) :
    ∀ p, (FilteredStream.view D.rightRecords (rows D p)).Pairwise
      (fun a b => key D a ≤ key D b) := by
  intro p
  have h := FilteredStream.array_sorted D.leftRecords D.rightRecords
    (fun x => D.wl x.semantic) (fun x => D.wl x.semantic) D.lowModulus D.modulus
    D.residue (primary D) (secondary D) D.positive D.mode _ p
  simpa only [rows, recordKey_eq D] using h

def start (D : RepresentationPairData n) : State D :=
  MergedReader.start (key D) (FilteredStream.read D.rightRecords)
    (FilteredStream.view D.rightRecords) (FilteredStream.reader _) (rows D) (rows_sorted D)

def next (D : RepresentationPairData n) (s : State D) :
    Option ((LeafRecord n × LeafRecord n) × State D) :=
  MergedReader.next (key D) (FilteredStream.read D.rightRecords)
    (FilteredStream.view D.rightRecords) (FilteredStream.reader _) s

def output (D : RepresentationPairData n) (s : State D) : List (LeafRecord n × LeafRecord n) :=
  MergedReader.output (key D) (FilteredStream.read D.rightRecords)
    (FilteredStream.view D.rightRecords) s

def mappedState (D : RepresentationPairData n) (s : State D) :=
  MergedReader.mapState RepresentationKeys.pairSemantic (cursorMap D) (sourceKey D)
    (FilteredStream.view D.rightRecords) (FilteredStream.view (D.rightRecords.map LeafRecord.semantic))
    (FilteredStream.view_map LeafRecord.semantic LeafRecord.semantic D.rightRecords) s

private def transportState {α β : Type*} {d : ℕ} (key : α × β → ℤ)
    {xs ys : Array β} (h : xs = ys)
    (s : MergedReader.State key (FilteredStream.view xs) d) :
    MergedReader.State key (FilteredStream.view ys) d := h ▸ s

private theorem transport_next {α β : Type*} {d : ℕ} (key : α × β → ℤ)
    {xs ys : Array β} (h : xs = ys)
    (s : MergedReader.State key (FilteredStream.view xs) d) :
    (MergedReader.next key (FilteredStream.read xs) (FilteredStream.view xs)
      (FilteredStream.reader _) s).map (fun z => (z.1, transportState key h z.2)) =
      MergedReader.next key (FilteredStream.read ys) (FilteredStream.view ys)
        (FilteredStream.reader _) (transportState key h s) := by
  subst ys
  simp [transportState]

private theorem transport_output {α β : Type*} {d : ℕ} (key : α × β → ℤ)
    {xs ys : Array β} (h : xs = ys)
    (s : MergedReader.State key (FilteredStream.view xs) d) :
    MergedReader.output key (FilteredStream.read xs) (FilteredStream.view xs) s =
      MergedReader.output key (FilteredStream.read ys) (FilteredStream.view ys)
        (transportState key h s) := by
  subst ys
  rfl

private theorem transport_start {α β : Type*} (left : Array α) {xs ys : Array β}
    (h : xs = ys) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted xs wr p) (ht : FilteredRow.SecondarySorted xs wr p P)
    (hs' : FilteredRow.PrimarySorted ys wr p) (ht' : FilteredRow.SecondarySorted ys wr p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) :
    transportState (FilteredStream.key wl wr P mode) h
      (FilteredStream.start left xs wl wr p P c hs ht hP mode) =
      FilteredStream.start left ys wl wr p P c hs' ht' hP mode := by
  subst ys
  rfl

def semanticState (D : RepresentationPairData n) (s : State D) : D.State :=
  transportState (sourceKey D) D.rightRecords_semantic (mappedState D s)

theorem next_map (D : RepresentationPairData n) (s : State D) :
    (next D s).map (fun z => (RepresentationKeys.pairSemantic z.1, mappedState D z.2)) =
      MergedReader.next (sourceKey D) (FilteredStream.read (D.rightRecords.map LeafRecord.semantic))
        (FilteredStream.view (D.rightRecords.map LeafRecord.semantic)) (FilteredStream.reader _)
        (mappedState D s) := by
  exact MergedReader.next_map RepresentationKeys.pairSemantic (cursorMap D) (sourceKey D)
    (FilteredStream.read D.rightRecords) (FilteredStream.read (D.rightRecords.map LeafRecord.semantic))
    (FilteredStream.read_map LeafRecord.semantic LeafRecord.semantic D.rightRecords)
    (FilteredStream.view D.rightRecords) (FilteredStream.view (D.rightRecords.map LeafRecord.semantic))
    (FilteredStream.view_map LeafRecord.semantic LeafRecord.semantic D.rightRecords)
    (FilteredStream.reader _) (FilteredStream.reader _) s

theorem output_map (D : RepresentationPairData n) (s : State D) :
    (output D s).map RepresentationKeys.pairSemantic =
      MergedReader.output (sourceKey D) (FilteredStream.read (D.rightRecords.map LeafRecord.semantic))
        (FilteredStream.view (D.rightRecords.map LeafRecord.semantic)) (mappedState D s) := by
  exact MergedReader.output_map RepresentationKeys.pairSemantic (cursorMap D) (sourceKey D)
    (FilteredStream.read D.rightRecords) (FilteredStream.read (D.rightRecords.map LeafRecord.semantic))
    (FilteredStream.read_map LeafRecord.semantic LeafRecord.semantic D.rightRecords)
    (FilteredStream.view D.rightRecords) (FilteredStream.view (D.rightRecords.map LeafRecord.semantic))
    (FilteredStream.view_map LeafRecord.semantic LeafRecord.semantic D.rightRecords) s

private theorem mapped_primary (D : RepresentationPairData n) :
    FilteredRow.PrimarySorted (D.rightRecords.map LeafRecord.semantic) D.wl D.lowModulus := by
  rw [D.rightRecords_semantic]
  exact ResidueSort.primary _ _ _ _

private theorem mapped_start_tree (D : RepresentationPairData n) :
    (mappedState D (start D)).tree =
      RowMerge.start (sourceKey D) (FilteredStream.read (D.rightRecords.map LeafRecord.semantic))
        (PaddedRows.rows
          (FilteredStream.rowArray (D.leftRecords.map LeafRecord.semantic)
            (D.rightRecords.map LeafRecord.semantic) D.wl D.wl D.lowModulus D.modulus
            D.residue (mapped_primary D) D.mode) (Nat.clog 2 D.leftArray.size)) := by
  have h := FilteredStream.initial_tree_map LeafRecord.semantic LeafRecord.semantic
    D.leftRecords D.rightRecords D.wl D.wl D.lowModulus D.modulus D.residue
    (primary D) (mapped_primary D) D.mode (Nat.clog 2 D.leftArray.size)
  rw [recordKey_eq D] at h
  exact h

private theorem state_ext {α σ : Type*} {key : α → ℤ} {view : σ → List α} {d : ℕ}
    {a b : MergedReader.State key view d} (h : a.tree = b.tree) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem mapped_secondary (D : RepresentationPairData n) :
    FilteredRow.SecondarySorted (D.rightRecords.map LeafRecord.semantic) D.wl
      D.lowModulus D.modulus := by
  rw [D.rightRecords_semantic]
  exact ResidueSort.secondary _ _ _ _

private theorem mapped_start (D : RepresentationPairData n) :
    mappedState D (start D) =
      FilteredStream.start D.leftArray (D.rightRecords.map LeafRecord.semantic)
        D.wl D.wl D.lowModulus D.modulus D.residue (mapped_primary D)
        (mapped_secondary D) D.positive D.mode := by
  apply state_ext
  simpa only [FilteredStream.start, MergedReader.start, D.leftRecords_semantic, sourceKey]
    using mapped_start_tree D

theorem semantic_start (D : RepresentationPairData n) : semanticState D (start D) = D.start := by
  unfold semanticState
  rw [mapped_start]
  exact transport_start D.leftArray D.rightRecords_semantic D.wl D.wl D.lowModulus
    D.modulus D.residue (mapped_primary D) (mapped_secondary D)
    (ResidueSort.primary _ _ _ _) (ResidueSort.secondary _ _ _ _) D.positive D.mode

theorem semantic_next (D : RepresentationPairData n) (s : State D) :
    (next D s).map (fun z => (RepresentationKeys.pairSemantic z.1, semanticState D z.2)) =
      D.read (semanticState D s) := by
  have h := congrArg (fun z => z.map (fun x =>
    (x.1, transportState (sourceKey D) D.rightRecords_semantic x.2))) (next_map D s)
  have ht := transport_next (sourceKey D) D.rightRecords_semantic (mappedState D s)
  have h' := h.trans ht
  simpa only [Option.map_map, Function.comp_def, semanticState,
    RepresentationPairData.read, RepresentationPairData.State, sourceKey] using h'

theorem semantic_output (D : RepresentationPairData n) (s : State D) :
    (output D s).map RepresentationKeys.pairSemantic = D.output (semanticState D s) := by
  exact (output_map D s).trans
    (transport_output (sourceKey D) D.rightRecords_semantic (mappedState D s))

theorem start_output_map (D : RepresentationPairData n) :
    (output D (start D)).map RepresentationKeys.pairSemantic = D.output D.start := by
  rw [semantic_output, semantic_start]

end LowSpaceSubsetSum.RepresentationStoredReader

end OAI
