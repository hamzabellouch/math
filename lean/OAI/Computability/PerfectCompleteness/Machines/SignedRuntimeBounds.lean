import OAI.Computability.PerfectCompleteness.Foundations.SignedCostEnvelope
import OAI.Computability.PerfectCompleteness.Foundations.SignedTupleSemantics
import OAI.Computability.PerfectCompleteness.Foundations.SourceKeyBoundsLemmas

namespace OAI


namespace PerfectCompleteness.SignedRuntimeBounds


open CanonicalKeys MetadataFreeSampler
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

def KeyBound {width : Nat} (T : Nat) (key : Key width) : Prop :=
  key.retained.length ≤ width ∧
    ∀ entry ∈ key.retained, KeyMetadataEncoding.entryID entry.2 ≤ T

def KeysBound {width : Nat} (T : Nat) (keys : List (Key width)) : Prop :=
  ∀ key ∈ keys, KeyBound T key

theorem keysBound_append {width T : Nat} {keys : List (Key width)} {key : Key width}
    (earlier : KeysBound T keys) (last : KeyBound T key) :
    KeysBound T (keys ++ [key]) := by
  intro candidate present
  rcases List.mem_append.mp present with present | present
  · exact earlier candidate present
  · have same : candidate = key := by simpa using present
    simpa only [same] using last

theorem endpoint_budget_le {width T count : Nat} {K : Type} [DecidableEq K]
    (source : Fin width → Fin 6 → K) (base : K → List Bool)
    (earlier : List (Key width)) (key : Key width)
    (sourceBound : CanonicalKeyMachine.sourceLength source base ≤ 4 * width * (T + 1))
    (earlierBound : KeysBound T earlier) (keyBound : KeyBound T key)
    (countBound : earlier.length + 1 ≤ count) :
    CanonicalEndpointMachine.budget source base earlier key ≤
      SignedCostEnvelope.endpointBound width T count := by
  have allBound := keysBound_append earlierBound keyBound
  have payloadBound := CanonicalVertexNames.payload_length_le key T keyBound.1 keyBound.2
  have streamBound :
      (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ≤
        CanonicalDictionaryNames.streamBound width T count := by
    have h := CanonicalVertexNames.stream_length_le (earlier ++ [key]) T
      (fun candidate present => (allBound candidate present).1)
      (fun candidate present => (allBound candidate present).2)
    apply h.trans
    apply Nat.mul_le_mul_left
    simpa only [List.length_append, List.length_singleton] using countBound
  have squareBound := Nat.pow_le_pow_left streamBound 2
  unfold CanonicalEndpointMachine.budget SignedCostEnvelope.endpointBound
  nlinarith

section Fold

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "width" => TreeCanonical.locationCount branch n t
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q

theorem fold_budget_le {K : Type} [DecidableEq K] (T count : Nat)
    (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (source : Fin width → Fin 6 → K)
    (work : Fin 10 → K) (countTape : K) (base : K → List Bool)
    (sourceBound : ∀ data : SignedTupleBodyMachine.Data width,
      CanonicalKeyMachine.sourceLength source
        (SignedTupleBodyMachine.tapes work countTape base data) ≤ 4 * width * (T + 1))
    (leftBound : ∀ i : Fin D, KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows signs i) .left ids vars))
    (rightBound : ∀ i : Fin D, KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows signs i) .right ids vars))
    (indices : List (Fin D)) (data : SignedTupleBodyMachine.Data width)
    (leftEarlier : KeysBound T data.leftKeys) (rightEarlier : KeysBound T data.rightKeys)
    (leftCount : data.leftKeys.length + indices.length ≤ count)
    (rightCount : data.rightKeys.length + indices.length ≤ count) :
    SignedTupleBodyMachine.budget hq large hn hbranch hrows signs ids vars
        source work countTape base indices data ≤
      indices.length * (2 * SignedCostEnvelope.endpointBound width T count + 4) := by
  induction indices generalizing data with
  | nil => simp only [SignedTupleBodyMachine.budget, List.length_nil, Nat.zero_mul, le_refl]
  | cons i indices ih =>
    let descriptor := SignedScheduleIndex.atIndex hq large hn hbranch hrows signs i
    have leftCount' : data.leftKeys.length + 1 ≤ count := by
      simp only [List.length_cons] at leftCount
      omega
    have rightCount' : data.rightKeys.length + 1 ≤ count := by
      simp only [List.length_cons] at rightCount
      omega
    have leftCost := endpoint_budget_le source
      (SignedTupleBodyMachine.tapes work countTape base data) data.leftKeys
      (CompletedEdgeMachine.key hq large descriptor .left ids vars)
      (sourceBound data) leftEarlier (leftBound i) leftCount'
    have rightCost := endpoint_budget_le source
      (SignedTupleBodyMachine.tapes work countTape base data) data.rightKeys
      (CompletedEdgeMachine.key hq large descriptor .right ids vars)
      (sourceBound data) rightEarlier (rightBound i) rightCount'
    have edgeCost : CompletedEdgeMachine.budget hq large descriptor source
        (SignedTupleBodyMachine.tapes work countTape base data)
        data.leftKeys data.rightKeys ids vars ≤
        2 * SignedCostEnvelope.endpointBound width T count + 1 := by
      unfold CompletedEdgeMachine.budget
      omega
    have nextLeft : KeysBound T
        (SignedTupleBodyMachine.next hq large descriptor ids vars data).leftKeys :=
      keysBound_append leftEarlier (leftBound i)
    have nextRight : KeysBound T
        (SignedTupleBodyMachine.next hq large descriptor ids vars data).rightKeys :=
      keysBound_append rightEarlier (rightBound i)
    have nextLeftCount :
        (SignedTupleBodyMachine.next hq large descriptor ids vars data).leftKeys.length +
          indices.length ≤ count := by
      simpa only [SignedTupleBodyMachine.next, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using leftCount
    have nextRightCount :
        (SignedTupleBodyMachine.next hq large descriptor ids vars data).rightKeys.length +
          indices.length ≤ count := by
      simpa only [SignedTupleBodyMachine.next, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rightCount
    have rest := ih (SignedTupleBodyMachine.next hq large descriptor ids vars data)
      nextLeft nextRight nextLeftCount nextRightCount
    change CompletedEdgeMachine.budget hq large descriptor source
        (SignedTupleBodyMachine.tapes work countTape base data)
        data.leftKeys data.rightKeys ids vars + 3 +
        SignedTupleBodyMachine.budget hq large hn hbranch hrows signs ids vars
          source work countTape base indices
          (SignedTupleBodyMachine.next hq large descriptor ids vars data) ≤ _
    calc
      _ ≤ (2 * SignedCostEnvelope.endpointBound width T count + 1) + 3 +
          indices.length * (2 * SignedCostEnvelope.endpointBound width T count + 4) :=
        Nat.add_le_add (Nat.add_le_add_right edgeCost 3) rest
      _ = (i :: indices).length *
          (2 * SignedCostEnvelope.endpointBound width T count + 4) := by
        simp only [List.length_cons]
        ring

end Fold


variable {branch : Nat → Nat} {n t : Nat}
  (input : NormalizedSourceInput.Input) (rows repeats : Nat → Nat)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "clauses" => NormalizedSourceInput.clauses input
local notation "T" => List.length (NormalizedSourceInput.bits input)
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "hq" => CanonicalLocalCompletion.alphabet_positive width δ
local notation "large" => CanonicalLocalCompletion.partitionWidth_le_alphabet width δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "C" => CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "localOrder" => CompletedVisitOrder.localOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "dataOfPrefix" => SignedTupleSemantics.dataOfPrefix
  (t := t) clauses rows repeats hn hbranch hrows δ

theorem completedOrder_length_le : (order).length ≤ D * (T + 1) ^ width := by
  rw [CompletedVisitOrder.completedOrder_length]
  exact Nat.mul_le_mul_left D
    (Nat.pow_le_pow_left ((SourceKeyBounds.clauseCount_le_bits input).trans (Nat.le_succ T)) width)

theorem left_atIndex_bound
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (i : Fin D) :
    KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i)
      .left (SignedTupleSemantics.sourceIDs source)
      (SignedTupleSemantics.sourceVariables clauses source)) := by
  let e := SignedTupleSemantics.occurrenceAt clauses rows repeats hn hbranch hrows δ source i
  have same := SignedTupleSemantics.left_key clauses rows repeats hn hbranch hrows δ e
  simp only [e, SignedTupleSemantics.descriptorOf_occurrenceAt,
    SignedTupleSemantics.occurrenceAt_source] at same
  rw [same]
  exact ⟨SourceKeyBounds.left_retained_length input rows repeats e.1,
    SourceKeyBounds.left_entryID_le input rows repeats e.1⟩

theorem right_atIndex_bound
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (i : Fin D) :
    KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i)
      .right (SignedTupleSemantics.sourceIDs source)
      (SignedTupleSemantics.sourceVariables clauses source)) := by
  let e := SignedTupleSemantics.occurrenceAt clauses rows repeats hn hbranch hrows δ source i
  have same := SignedTupleSemantics.right_key clauses rows repeats hn hbranch hrows δ e
  simp only [e, SignedTupleSemantics.descriptorOf_occurrenceAt,
    SignedTupleSemantics.occurrenceAt_source] at same
  rw [same]
  exact ⟨SourceKeyBounds.right_retained_length input rows repeats e.1,
    SourceKeyBounds.right_entryID_le input rows repeats e.1⟩

theorem left_prefix_bound (earlier : List C) (tail : List Bool) :
    KeysBound T (dataOfPrefix earlier tail).leftKeys := by
  intro key present
  change key ∈ earlier.map _ at present
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
  exact ⟨SourceKeyBounds.left_retained_length input rows repeats e.1,
    SourceKeyBounds.left_entryID_le input rows repeats e.1⟩

theorem right_prefix_bound (earlier : List C) (tail : List Bool) :
    KeysBound T (dataOfPrefix earlier tail).rightKeys := by
  intro key present
  change key ∈ earlier.map _ at present
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
  exact ⟨SourceKeyBounds.right_retained_length input rows repeats e.1,
    SourceKeyBounds.right_entryID_le input rows repeats e.1⟩

theorem bodyBudget_le_envelope {Extra : Type} [DecidableEq Extra]
    (indices : NormalizedTarget.SourceTuple (branch := branch) (n := n) (t := t) input)
    (base : SignedTupleLayout.Tape width Extra → List Bool)
    (physical : SignedTupleLayout.Input input.formula indices base)
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ localOrder (NormalizedTarget.tupleQuestion input indices) ++ suffix) :
    SignedTupleBodyMachine.bodyBudget
        (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows input.formula indices base
        (dataOfPrefix earlier tail) ≤ SignedCostEnvelope.bodyBound width D T := by
  let source := NormalizedTarget.tupleQuestion input indices
  have countBound : earlier.length + D ≤ D * (T + 1) ^ width := by
    have total := completedOrder_length_le (t := t) input rows repeats hn hbranch hrows δ
    rw [split, List.length_append, List.length_append,
      CompletedVisitOrder.localOrder_length] at total
    omega
  have ids_eq : SignedTupleLayout.ids input.formula indices =
      SignedTupleSemantics.sourceIDs source := by
    simp only [source, NormalizedTarget.tupleQuestion, SignedTupleSemantics.sourceIDs_tuple]
    rfl
  have vars_eq : SignedTupleLayout.vars input.formula indices =
      SignedTupleSemantics.sourceVariables clauses source := by
    simp only [source, NormalizedTarget.tupleQuestion, SignedTupleSemantics.sourceVariables_tuple]
    rfl
  have selectedLeft (i : Fin D) : KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows
        (SourceTupleScheduleMachine.sourceSigns input.formula indices) i)
      .left (SignedTupleLayout.ids input.formula indices) (SignedTupleLayout.vars input.formula indices)) := by
    rw [NormalizedTarget.sourceSigns_eq, ids_eq, vars_eq]
    exact left_atIndex_bound input rows repeats hn hbranch hrows δ source i
  have selectedRight (i : Fin D) : KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows
        (SourceTupleScheduleMachine.sourceSigns input.formula indices) i)
      .right (SignedTupleLayout.ids input.formula indices) (SignedTupleLayout.vars input.formula indices)) := by
    rw [NormalizedTarget.sourceSigns_eq, ids_eq, vars_eq]
    exact right_atIndex_bound input rows repeats hn hbranch hrows δ source i
  have leftCount : (dataOfPrefix earlier tail).leftKeys.length +
      (SignedTupleBodyMachine.allStages (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hn hbranch hrows).length ≤ D * (T + 1) ^ width := by
    simpa only [SignedTupleSemantics.dataOfPrefix, ExactTargetOnlineEncoding.leftKeys,
      List.length_map, SignedTupleBodyMachine.allStages, List.length_ofFn] using countBound
  have rightCount : (dataOfPrefix earlier tail).rightKeys.length +
      (SignedTupleBodyMachine.allStages (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hn hbranch hrows).length ≤ D * (T + 1) ^ width := by
    simpa only [SignedTupleSemantics.dataOfPrefix, ExactTargetOnlineEncoding.rightKeys,
      List.length_map, SignedTupleBodyMachine.allStages, List.length_ofFn] using countBound
  have folded := fold_budget_le hq large hn hbranch hrows T (D * (T + 1) ^ width)
    (SourceTupleScheduleMachine.sourceSigns input.formula indices)
    (SignedTupleLayout.ids input.formula indices) (SignedTupleLayout.vars input.formula indices)
    SignedTupleLayout.metadata SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount
    (SignedTupleLayout.preparedTapes input.formula indices base)
    (SignedSourceCost.prepared_sourceLength_le input indices base physical)
    selectedLeft selectedRight (SignedTupleBodyMachine.allStages hn hbranch hrows)
    (dataOfPrefix earlier tail)
    (left_prefix_bound input rows repeats hn hbranch hrows δ earlier tail)
    (right_prefix_bound input rows repeats hn hbranch hrows δ earlier tail) leftCount rightCount
  have preparation := SignedTuplePreparationMachine.budget_le width T
  unfold SignedTupleBodyMachine.bodyBudget SignedCostEnvelope.bodyBound
  change 1 + SignedTuplePreparationMachine.budget width T + _ + 7 * width * (T + 2) + 1 ≤ _
  simp only [SignedTupleBodyMachine.allStages, List.length_ofFn] at folded ⊢
  change _ ≤ D * (2 * SignedCostEnvelope.endpointBound width T (D * (T + 1) ^ width) + 4)
    at folded
  omega

theorem bodyBudget_le_polynomial {Extra : Type} [DecidableEq Extra]
    (indices : NormalizedTarget.SourceTuple (branch := branch) (n := n) (t := t) input)
    (base : SignedTupleLayout.Tape width Extra → List Bool)
    (physical : SignedTupleLayout.Input input.formula indices base)
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ localOrder (NormalizedTarget.tupleQuestion input indices) ++ suffix) :
    SignedTupleBodyMachine.bodyBudget
        (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows input.formula indices base
        (dataOfPrefix earlier tail) ≤
      SignedCostEnvelope.bodyCoeff width D * (T + 1) ^ SignedCostEnvelope.degree width :=
  (bodyBudget_le_envelope input rows repeats hn hbranch hrows δ
    indices base physical earlier suffix tail split).trans (SignedCostEnvelope.bodyBound_le width D T)

theorem outerBudget_le_polynomial :
    (SignedCostEnvelope.bodyCoeff width D * (T + 1) ^ SignedCostEnvelope.degree width +
        2 * width) * (NormalizedSourceInput.clauseCount input) ^ width ≤
      (SignedCostEnvelope.bodyCoeff width D + 2 * width) *
        (T + 1) ^ (SignedCostEnvelope.degree width + width) := by
  have visits : (NormalizedSourceInput.clauseCount input) ^ width ≤ (T + 1) ^ width :=
    Nat.pow_le_pow_left ((SourceKeyBounds.clauseCount_le_bits input).trans (Nat.le_succ T)) width
  have positive : 1 ≤ (T + 1) ^ SignedCostEnvelope.degree width :=
    Nat.one_le_pow _ _ (Nat.succ_pos T)
  have overhead : 2 * width ≤ 2 * width * (T + 1) ^ SignedCostEnvelope.degree width := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * width) positive
  calc
    _ ≤ ((SignedCostEnvelope.bodyCoeff width D + 2 * width) *
        (T + 1) ^ SignedCostEnvelope.degree width) * (T + 1) ^ width := by
      apply Nat.mul_le_mul _ visits
      rw [Nat.add_mul]
      exact Nat.add_le_add_left overhead _
    _ = _ := by rw [Nat.pow_add]; ring

end

end PerfectCompleteness.SignedRuntimeBounds

end OAI
