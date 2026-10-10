import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedParentJoin
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.JoinReaderMap
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredReader

namespace OAI

/-! # Refinement of the stored-record parent collector

The state casts below change only the proof of the key evaluator. Semantic
erasure preserves the complete stopped result, including occurrence order,
query/report/copy counters and early overflow.
-/

namespace LowSpaceSubsetSum

namespace MergedReader

def rekey {α σ : Type*} {key key' : α → ℤ} {view : σ → List α} {d : ℕ}
    (h : key = key') (s : State key view d) : State key' view d := h ▸ s

theorem rekey_inverse {α σ : Type*} {key key' : α → ℤ} {view : σ → List α} {d : ℕ}
    (h : key = key') (s : State key' view d) : rekey h (rekey h.symm s) = s := by
  cases h
  rfl

theorem rekey_next {α σ : Type*} {key key' : α → ℤ} {view : σ → List α} {d : ℕ}
    (h : key = key') (read : σ → Option (α × σ)) (hr : RowMerge.IsReader read view)
    (s : State key view d) :
    (next key read view hr s).map (Prod.map id (rekey h)) =
      next key' read view hr (rekey h s) := by
  cases h
  change (next key read view hr s).map id = next key read view hr s
  exact Option.map_id'

end MergedReader

namespace StoredParentExecution

variable {n : ℕ}

abbrev State (D : RepresentationParentData n) (F : IndexedMask n) (j : Fin 2) :=
  CountedParentJoin.State D.input F D.modulus (D.pair j).mode
    (D.pair j).rightRecords (Nat.clog 2 (D.pair j).leftArray.size)

theorem key_eq (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    (fun x => (RepresentationKeys.pairKey D.input F D.modulus (D.pair j).mode x).1) =
      RepresentationStoredReader.key (D.pair j) := by
  funext x
  exact RepresentationKeys.parent_pairKey_value D F hF j x

def toStored (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (s : State D F j) :
    RepresentationStoredReader.State (D.pair j) := MergedReader.rekey (key_eq D F hF j) s

def start (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) : State D F j :=
  MergedReader.rekey (key_eq D F hF j).symm (RepresentationStoredReader.start (D.pair j))

def semanticState (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (s : State D F j) : (D.pair j).State :=
  RepresentationStoredReader.semanticState (D.pair j) (toStored D F hF j s)

theorem semantic_start (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    semanticState D F hF j (start D F hF j) = (D.pair j).start := by
  simp only [semanticState, toStored, start, MergedReader.rekey_inverse]
  exact RepresentationStoredReader.semantic_start (D.pair j)

def read (D : RepresentationParentData n) (F : IndexedMask n) (j : Fin 2) :=
  RepresentationKeys.read D.input F D.modulus (D.pair j).mode (D.pair j).rightRecords
    (d := Nat.clog 2 (D.pair j).leftArray.size)

theorem semantic_read (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (s : State D F j) :
    (D.pair j).read (semanticState D F hF j s) =
      (read D F j s).1.map (Prod.map RepresentationKeys.pairSemantic
        (semanticState D F hF j)) := by
  have hv := RepresentationKeys.read_value D.input F D.modulus (D.pair j).mode
    (D.pair j).rightRecords s
  simp only [FilteredStream.countedRead_value] at hv
  change _ = (RepresentationKeys.read _ _ _ _ _ s).1.map _
  rw [hv]
  have hm := MergedReader.rekey_next (key_eq D F hF j)
    (FilteredStream.read (D.pair j).rightRecords) (FilteredStream.reader _) s
  have hs := RepresentationStoredReader.semantic_next (D.pair j) (toStored D F hF j s)
  change (D.pair j).read (RepresentationStoredReader.semanticState (D.pair j)
    (toStored D F hF j s)) = _
  rw [← hs]
  change (MergedReader.next _ _ _ _ (MergedReader.rekey (key_eq D F hF j) s)).map _ = _
  rw [← hm]
  simp only [Option.map_map, Function.comp_def, Prod.map, id_eq]
  rfl

def collect (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) :=
  CountedParentJoin.run D.input F D.modulus D.parentResidue D.capacity B
    (D.pair 0).rightRecords (D.pair 1).rightRecords
    (D.pair 0).lengthBound (D.pair 1).lengthBound
    ((D.pair 0).lengthBound + (D.pair 1).lengthBound + 1)
    (start D F hF 0) (start D F hF 1)

def erase (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) :=
  fun out => StreamJoin.mapReadersStopped (semanticState D F hF 0) (semanticState D F hF 1)
    (StreamJoin.mapStopped (StoredDictionaryJoin.erase D.input D.capacity) out)

theorem collect_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) :
    erase D F hF (collect D F hF B).1 = D.collect B := by
  have hv := StoredDictionaryJoin.run_value D.input D.capacity
    (read D F 0) (RepresentationKeys.pairKey D.input F D.modulus .direct)
    (read D F 1) (RepresentationKeys.pairKey D.input F D.modulus (.complementary D.parentResidue))
    CountedParentJoin.cells (CountedRepresentationEmit.emit D.input F)
    (CountedParentJoin.snapshot D.input F D.modulus (.complementary D.parentResidue)
      (D.pair 1).rightRecords)
    (CountedParentJoin.snapshot_value _ _ _ _ _)
    B (D.pair 0).lengthBound (D.pair 1).lengthBound
    ((D.pair 0).lengthBound + (D.pair 1).lengthBound + 1)
    (start D F hF 0) (start D F hF 1)
  change StreamJoin.mapReadersStopped _ _
    (StreamJoin.mapStopped _ (collect D F hF B).1) = _
  change StreamJoin.mapStopped _ (collect D F hF B).1 = _ at hv
  rw [hv]
  have hk (j : Fin 2) :
      (fun x => (RepresentationKeys.pairKey D.input F D.modulus (D.pair j).mode x).1) =
        (fun x => D.key j (RepresentationKeys.pairSemantic x)) :=
    funext (RepresentationKeys.parent_pairKey_value D F hF j)
  have he : (fun x y => (CountedRepresentationEmit.emit D.input F x y).1.map StoredEntry.semantic) =
      (fun x y => D.emit (RepresentationKeys.pairSemantic x) (RepresentationKeys.pairSemantic y)) :=
    funext fun x => funext fun y => CountedRepresentationEmit.emit_value D F hF x y
  change StreamJoin.mapReadersStopped _ _
    (StreamJoin.stopped (fun s => (read D F 0 s).1)
      (fun x => (RepresentationKeys.pairKey D.input F D.modulus (D.pair 0).mode x).1)
      (fun s => (read D F 1 s).1)
      (fun x => (RepresentationKeys.pairKey D.input F D.modulus (D.pair 1).mode x).1)
      _ _ _ _ _ _ _ _) = _
  conv_lhs => arg 3; arg 2; rw [hk 0]
  conv_lhs => arg 3; arg 4; rw [hk 1]
  conv_lhs => arg 3; arg 5; rw [he]
  have hcallback :
      RecordedDictionary.callback D.capacity (WeightEncoding.entryKey D.input)
        (fun x y => D.emit (RepresentationKeys.pairSemantic x) (RepresentationKeys.pairSemantic y)) =
      (fun x y => RecordedDictionary.callback D.capacity (WeightEncoding.entryKey D.input)
        D.emit (RepresentationKeys.pairSemantic x) (RepresentationKeys.pairSemantic y)) := rfl
  conv_lhs => arg 3; arg 5; rw [hcallback]
  unfold StreamJoin.stopped
  rw [StreamJoin.stoppedAcc_mapReaders RepresentationKeys.pairSemantic
    RepresentationKeys.pairSemantic (semanticState D F hF 0) (semanticState D F hF 1)
    (fun s => (read D F 0 s).1) (D.pair 0).read
    (fun s => (read D F 1 s).1) (D.pair 1).read
    (semantic_read D F hF 0) (semantic_read D F hF 1)
    (D.key 0) (D.key 1) (RecordedDictionary.callback D.capacity
      (WeightEncoding.entryKey D.input) D.emit)]
  change StreamJoin.stoppedAcc _ _ _ _ _ _ _ _ _
    (StreamJoin.start (semanticState D F hF 0 (start D F hF 0))
      (semanticState D F hF 1 (start D F hF 1)) RecordedDictionary.empty) = _
  rw [semantic_start, semantic_start]
  rfl

private theorem erase_charge (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs)
    (out : StreamJoin.StoppedResult (State D F 0) (State D F 1)
      (StoredEntry.Dictionary D.input D.capacity)) (M K : ℕ) :
    M * ((erase D F hF out).state.queries + (erase D F hF out).state.reports + 1) +
      K * (erase D F hF out).state.copies =
    M * (out.state.queries + out.state.reports + 1) + K * out.state.copies := rfl

theorem collect_work (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (hn : 10000 ≤ n)
    (hd₀ : Nat.clog 2 (D.pair 0).leftArray.size ≤ n)
    (hd₁ : Nat.clog 2 (D.pair 1).leftArray.size ≤ n)
    (hcopy : (12 * n + 32) * 2 ^ (Nat.clog 2 (D.pair 1).leftArray.size + 1) ≤ B) :
    (collect D F hF B).2 ≤ inputScale D.input ^ 6 *
      ((D.collect B).state.queries + (D.collect B).state.reports + 1) +
        B * (D.collect B).state.copies := by
  have hw : (collect D F hF B).2 ≤ inputScale D.input ^ 6 *
      ((collect D F hF B).1.state.queries + (collect D F hF B).1.state.reports + 1) +
      B * (collect D F hF B).1.state.copies :=
    CountedParentJoin.run_work D.input F D.modulus D.parentResidue D.capacity B
    (D.pair 0).rightRecords (D.pair 1).rightRecords
    (d₁ := Nat.clog 2 (D.pair 0).leftArray.size)
    (d₂ := Nat.clog 2 (D.pair 1).leftArray.size)
    (D.pair 0).lengthBound (D.pair 1).lengthBound
    ((D.pair 0).lengthBound + (D.pair 1).lengthBound + 1)
    (start D F hF 0) (start D F hF 1) hn hd₀ hd₁ hcopy
  have he := congrArg (fun x : StreamJoin.StoppedResult (D.pair 0).State (D.pair 1).State
        (RecordedDictionary.State (Entry (Fin n))) => inputScale D.input ^ 6 *
      (x.state.queries + x.state.reports + 1) + B * x.state.copies) (collect_value D F hF B)
  rw [erase_charge D F hF (collect D F hF B).1 (inputScale D.input ^ 6) B] at he
  exact hw.trans_eq he

end StoredParentExecution
end LowSpaceSubsetSum

end OAI
