import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Machines.ExactTargetOnlineEncoding
import OAI.Computability.PerfectCompleteness.Machines.SignedTupleBodyMachine

namespace OAI


namespace PerfectCompleteness.SignedTupleSemantics


open MetadataFreeSampler
open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "hq" => CanonicalLocalCompletion.alphabet_positive width δ
local notation "large" => CanonicalLocalCompletion.partitionWidth_le_alphabet width δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "C" => CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ
local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats
local notation "equiv" => CompletedSignedLaw.completedEquiv (t := t) clauses rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "localOrder" => CompletedVisitOrder.localOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "targetEntry" => ExactPreliminaryTarget.entry
  (t := t) clauses rows repeats hn hbranch hrows δ

def sourceIDs (source : PreliminarySampler.Questions branch n t m) : Fin width → Nat :=
  fun i => (SourceQuestionOrder.questionToTuple source i).val

def sourceVariables (source : PreliminarySampler.Questions branch n t m) :
    Fin width → Fin 3 → Nat :=
  fun i j => ((clauses (SourceQuestionOrder.questionToTuple source i)).variable j).val

omit [NeZero m] in
@[simp] theorem sourceIDs_tuple (indices : Fin width → Fin m) :
    sourceIDs (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) =
      fun i => (indices i).val := by
  exact congrArg (fun tuple : Fin width → Fin m => fun i => (tuple i).val)
    (SourceQuestionOrder.questionToTuple_tupleToQuestion
      (branch := branch) (n := n) (t := t) indices)

omit [NeZero m] in
@[simp] theorem sourceVariables_tuple (indices : Fin width → Fin m) :
    sourceVariables clauses
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) =
      fun i j => ((clauses (indices i)).variable j).val := by
  exact congrArg
    (fun tuple : Fin width → Fin m => fun i j => ((clauses (tuple i)).variable j).val)
    (SourceQuestionOrder.questionToTuple_tupleToQuestion
      (branch := branch) (n := n) (t := t) indices)

omit [NeZero m] in
theorem sourceIDs_eq (source : PreliminarySampler.Questions branch n t m) :
    sourceIDs source = fun i => DescriptorKeyTemplate.occurrence
      (TreeCanonical.numberedSlots (sourceSlots clauses source) i) := rfl

omit [NeZero m] in
theorem sourceVariables_eq (source : PreliminarySampler.Questions branch n t m) :
    sourceVariables clauses source = fun i => DescriptorKeyTemplate.variableIDs
      (TreeCanonical.numberedSlots (sourceSlots clauses source) i) := rfl

def descriptorOf (e : C) : SignedCompletionSchedule.Descriptor
    (rows := rows) (repeats := repeats) hq large :=
  ⟨sourceSigns clauses (equiv e).1, (equiv e).2⟩

theorem descriptorOf_tape (e : C) :
    DescriptorKeyTemplate.tapeInput hq large
        (descriptorOf clauses rows repeats hn hbranch hrows δ e) =
      MetadataFreeTape.encodeRaw clauses rows repeats e.1 := rfl

theorem left_key (e : C) :
    CompletedEdgeMachine.key hq large (descriptorOf clauses rows repeats hn hbranch hrows δ e)
        .left (sourceIDs e.1.1.1) (sourceVariables clauses e.1.1.1) =
      CanonicalGame.leftKey F e.1 := by
  rcases e with ⟨raw, seed⟩
  exact (DescriptorKeyTemplate.recover_left clauses raw).trans
    (HierarchicalGame.leftKey_eq
      (PreliminarySampler.family clauses branch n t rows repeats) raw).symm

theorem right_key (e : C) :
    CompletedEdgeMachine.key hq large (descriptorOf clauses rows repeats hn hbranch hrows δ e)
        .right (sourceIDs e.1.1.1) (sourceVariables clauses e.1.1.1) =
      CanonicalGame.rightKey F e.1 := by
  rcases e with ⟨raw, seed⟩
  exact (DescriptorKeyTemplate.recover_right clauses raw).trans
    (HierarchicalGame.rightKey_eq
      (PreliminarySampler.family clauses branch n t rows repeats) raw).symm

omit [NeZero m] in
private theorem projection_ext {alphabet : Nat} {x y : ProjectionTable alphabet}
    (same : ∀ a : Fin (2 * alphabet), x.images[a] = y.images[a]) : x = y := by
  have images : x.images = y.images := by
    apply Vector.ext
    intro i hi
    exact same ⟨i, hi⟩
  cases x
  cases y
  cases images
  rfl

theorem projection_eq (e : C) :
    DescriptorProjectionMachine.projection hq large
        (descriptorOf clauses rows repeats hn hbranch hrows δ e) =
      (targetEntry e).projection  := by
  apply projection_ext (n := n) (alphabet := q)
  intro a
  have hp := DescriptorProjectionMachine.projection_apply
    (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
    hq large (descriptorOf (branch := branch) (n := n) (t := t) (v := v) (m := m)
      clauses rows repeats hn hbranch hrows δ e) a
  apply hp.trans
  delta ExactPreliminaryTarget.entry
  rw [ProjectionTable.ofMap_apply]
  exact CompletedSignedLaw.descriptorTable_eq_map
    (branch := branch) (n := n) (t := t) (v := v) (m := m)
    clauses rows repeats hn hbranch hrows δ e a

def occurrenceAt (source : PreliminarySampler.Questions branch n t m) (i : Fin D) : C :=
  (equiv).symm ⟨source,
    (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i).2⟩

theorem occurrenceAt_source (source : PreliminarySampler.Questions branch n t m) (i : Fin D) :
    (occurrenceAt clauses rows repeats hn hbranch hrows δ source i).1.1.1 = source :=
  CompletedSignedLaw.completedEquiv_symm_source (t := t) clauses rows repeats hn hbranch hrows δ _

theorem descriptorOf_occurrenceAt (source : PreliminarySampler.Questions branch n t m) (i : Fin D) :
    descriptorOf clauses rows repeats hn hbranch hrows δ
        (occurrenceAt clauses rows repeats hn hbranch hrows δ source i) =
      SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i := by
  have roundtrip := congrArg
    (fun x : CompletedSignedLaw.SignedCompleted (branch := branch) (n := n) (t := t)
        clauses rows repeats δ =>
      (⟨sourceSigns clauses x.1, x.2⟩ :
        SignedCompletionSchedule.Descriptor (rows := rows) (repeats := repeats) hq large))
    ((equiv).apply_symm_apply ⟨source,
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i).2⟩)
  exact roundtrip.trans (by rfl)

theorem ofFn_occurrenceAt (source : PreliminarySampler.Questions branch n t m) :
    List.ofFn (occurrenceAt clauses rows repeats hn hbranch hrows δ source) = localOrder source := by
  have localSchedule :
      List.ofFn (fun i : Fin D =>
        (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i).2) =
        SignedCompletionSchedule.schedule hq large hn hbranch hrows (sourceSigns clauses source) := by
    let xs := SignedCompletionSchedule.schedule
      (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
      hq large hn hbranch hrows (sourceSigns clauses source)
    have hlen : xs.length = D :=
      SignedCompletionSchedule.schedule_length
        (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows (sourceSigns clauses source)
    change List.ofFn (fun i : Fin D => xs.get (Fin.cast hlen.symm i)) = xs
    have roundtrip := (List.ofFn_congr hlen xs.get).symm
    rw [List.ofFn_get] at roundtrip
    exact roundtrip
  calc
    _ = (List.ofFn (fun i : Fin D =>
        (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i).2)).map
          (fun outcome => (equiv).symm ⟨source, outcome⟩) := List.ofFn_comp' _ _
    _ = localOrder source := by rw [localSchedule]; rfl

theorem map_finRange_occurrenceAt (source : PreliminarySampler.Questions branch n t m) :
    (List.finRange D).map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) =
      localOrder source := by
  rw [← List.ofFn_eq_map]
  exact ofFn_occurrenceAt clauses rows repeats hn hbranch hrows δ source

def dataOfPrefix (earlier : List C) (tail : List Bool) : SignedTupleBodyMachine.Data width where
  leftKeys := ExactTargetOnlineEncoding.leftKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier
  rightKeys := ExactTargetOnlineEncoding.rightKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier
  reversedOutput := (earlier.flatMap (fun e => encodeWords (Encoding.edgeWords (targetEntry e)))).reverse ++ tail
  count := earlier.length

theorem edgeBits_eq_entry (earlier suffix : List C) (e : C)
    (split : order = earlier ++ e :: suffix) :
    CompletedEdgeMachine.edgeBits hq large (descriptorOf clauses rows repeats hn hbranch hrows δ e)
        (ExactTargetOnlineEncoding.leftKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
        (ExactTargetOnlineEncoding.rightKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
        (sourceIDs e.1.1.1) (sourceVariables clauses e.1.1.1) =
      encodeWords (Encoding.edgeWords (targetEntry e)) := by
  rw [CompletedEdgeMachine.edgeBits_eq, left_key, right_key,
    DescriptorProjectionMachine.outputBits, DescriptorProjectionMachine.outputWords, projection_eq,
    ExactTargetOnlineEncoding.left_online (t := t) clauses rows repeats hn hbranch hrows δ
      earlier suffix e split,
    ExactTargetOnlineEncoding.right_online (t := t) clauses rows repeats hn hbranch hrows δ
      earlier suffix e split]
  simp only [Encoding.edgeWords, encodeWords_append, encodeWords, List.append_nil, List.append_assoc]

theorem next_eq_append (earlier suffix : List C) (e : C) (tail : List Bool)
    (split : order = earlier ++ e :: suffix) :
    SignedTupleBodyMachine.next hq large (descriptorOf clauses rows repeats hn hbranch hrows δ e)
        (sourceIDs e.1.1.1) (sourceVariables clauses e.1.1.1)
        (dataOfPrefix clauses rows repeats hn hbranch hrows δ earlier tail) =
      dataOfPrefix clauses rows repeats hn hbranch hrows δ (earlier ++ [e]) tail := by
  have hbits := edgeBits_eq_entry clauses rows repeats hn hbranch hrows δ earlier suffix e split
  simp only [ExactTargetOnlineEncoding.leftKeys, ExactTargetOnlineEncoding.rightKeys] at hbits
  simp only [SignedTupleBodyMachine.next, dataOfPrefix, left_key, right_key,
    hbits,
    ExactTargetOnlineEncoding.leftKeys, ExactTargetOnlineEncoding.rightKeys,
    List.map_append, List.map_cons, List.map_nil, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append,
    List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc]

theorem next_atIndex_eq (source : PreliminarySampler.Questions branch n t m) (i : Fin D)
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ occurrenceAt clauses rows repeats hn hbranch hrows δ source i :: suffix) :
    SignedTupleBodyMachine.next hq large
        (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i)
        (sourceIDs source) (sourceVariables clauses source)
        (dataOfPrefix clauses rows repeats hn hbranch hrows δ earlier tail) =
      dataOfPrefix clauses rows repeats hn hbranch hrows δ
        (earlier ++ [occurrenceAt clauses rows repeats hn hbranch hrows δ source i]) tail := by
  simpa only [descriptorOf_occurrenceAt, occurrenceAt_source] using
    next_eq_append clauses rows repeats hn hbranch hrows δ earlier suffix
      (occurrenceAt clauses rows repeats hn hbranch hrows δ source i) tail split

theorem result_eq_append (source : PreliminarySampler.Questions branch n t m)
    (indices : List (Fin D)) (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++
      indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix) :
    SignedTupleBodyMachine.result hq large hn hbranch hrows (sourceSigns clauses source)
        (sourceIDs source) (sourceVariables clauses source) indices
        (dataOfPrefix clauses rows repeats hn hbranch hrows δ earlier tail) =
      dataOfPrefix clauses rows repeats hn hbranch hrows δ
        (earlier ++ indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source)) tail := by
  induction indices generalizing earlier with
  | nil => simp only [SignedTupleBodyMachine.result, List.map_nil, List.append_nil]
  | cons i indices ih =>
    let e := occurrenceAt clauses rows repeats hn hbranch hrows δ source i
    have currentSplit : order = earlier ++ e ::
        (indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix) := by
      simpa only [e, List.map_cons, List.append_assoc, List.cons_append] using split
    rw [SignedTupleBodyMachine.result,
      next_atIndex_eq clauses rows repeats hn hbranch hrows δ source i earlier
        (indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix) tail currentSplit]
    have restSplit : order = (earlier ++ [e]) ++
        indices.map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix := by
      simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
        using currentSplit
    simpa only [e, List.map_cons, List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append] using
      ih (earlier ++ [e]) restSplit

theorem full_result_eq (source : PreliminarySampler.Questions branch n t m)
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ localOrder source ++ suffix) :
    SignedTupleBodyMachine.result hq large hn hbranch hrows (sourceSigns clauses source)
        (sourceIDs source) (sourceVariables clauses source) (List.finRange D)
        (dataOfPrefix clauses rows repeats hn hbranch hrows δ earlier tail) =
      dataOfPrefix clauses rows repeats hn hbranch hrows δ (earlier ++ localOrder source) tail := by
  have indexedSplit : order = earlier ++
      (List.finRange D).map (occurrenceAt clauses rows repeats hn hbranch hrows δ source) ++ suffix := by
    rwa [map_finRange_occurrenceAt]
  simpa only [map_finRange_occurrenceAt] using
    result_eq_append clauses rows repeats hn hbranch hrows δ source (List.finRange D)
      earlier suffix tail indexedSplit

end
end PerfectCompleteness.SignedTupleSemantics

end OAI
