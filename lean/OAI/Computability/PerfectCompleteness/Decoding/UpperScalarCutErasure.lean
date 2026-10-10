import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutReconstructionLemmas
import OAI.Computability.PerfectCompleteness.Sampling.OriginalCutPairLaw

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutErasure

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

def assocTapeEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    WholeArraySampler.Tape rows repeats ((p.append r).append q) slots ≃
      WholeArraySampler.Tape rows repeats (p.append (r.append q)) slots :=
  Equiv.cast (congrArg (fun path => WholeArraySampler.Tape rows repeats path slots)
    (p.append_assoc r q))

private theorem evaluate_cast (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {u v : Path branch n k} (h : u = v)
    (tape : WholeArraySampler.Tape rows repeats u slots) :
    WholeArraySampler.evaluate rows repeats v slots
        (Equiv.cast (congrArg (fun path => WholeArraySampler.Tape rows repeats path slots) h) tape) =
      WholeArraySampler.evaluate rows repeats u slots tape := by
  cases h
  rfl

theorem evaluate_assocTapeEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats ((p.append r).append q) slots) :
    WholeArraySampler.evaluate rows repeats (p.append (r.append q)) slots
        (assocTapeEquiv rows repeats p r q slots tape) =
      WholeArraySampler.evaluate rows repeats ((p.append r).append q) slots tape :=
  evaluate_cast rows repeats slots (p.append_assoc r q) tape

private theorem cast_step_selected (rows repeats : Nat → Nat) (child : Fin (branch n))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    {u v : Path branch n k} (h : u = v)
    (tape : WholeArraySampler.Tape rows repeats (.step child u) slots) :
    (Equiv.cast (congrArg (fun path => WholeArraySampler.Tape rows repeats path slots)
        (congrArg (Path.step child) h)) tape) (.inr (.inl ())) =
      Equiv.cast (congrArg
        (fun path => WholeArraySampler.Tape rows repeats path (childSlots slots child)) h)
        (tape (.inr (.inl ()))) := by
  cases h
  rfl

theorem assocTapeEquiv_selected (rows repeats : Nat → Nat) (child : Fin (branch n))
    (p : Path branch n j) (r : Path branch j i) (q : Path branch i k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (((Path.step child p).append r).append q) slots) :
    (assocTapeEquiv rows repeats (.step child p) r q slots tape) (.inr (.inl ())) =
      assocTapeEquiv rows repeats p r q (childSlots slots child) (tape (.inr (.inl ()))) :=
  cast_step_selected rows repeats child slots (p.append_assoc r q) tape

theorem extract_assocTapeEquiv (rows repeats : Nat → Nat) (p : Path branch n j) :
    ∀ (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots),
      WholeArraySubtreeSplit.extract rows repeats p (r.append (.step chosen q)) slots
          (assocTapeEquiv rows repeats p r (.step chosen q) slots tape) =
        UpperScalarCutBucket.descendTape rows repeats p r chosen q slots tape := by
  induction p with
  | refl n => intro r chosen q slots tape; rfl
  | step child p ih =>
      intro r chosen q slots tape
      rw [WholeArraySubtreeSplit.extract_step, assocTapeEquiv_selected]
      exact ih r chosen q (childSlots slots child) (tape (.inr (.inl ())))

def upperReadRecord (rows repeats : Nat → Nat) :
    {n j i k : Nat} → (p : Path branch n (j + 1)) →
      (r : Path branch (j + 1) (i + 1)) → (chosen : Fin (branch i)) → (q : Path branch i k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots →
          OriginalWholeCut.Record rows repeats p slots
  | _, _, _, _, p, .refl _, chosen, q, slots, tape =>
      OriginalWholeCut.readRecord rows repeats p chosen q slots tape
  | _, _, _, _, p, .step upperChild tail, chosen, q, slots, tape =>
      OriginalWholeCut.readRecord rows repeats p upperChild (tail.append (.step chosen q)) slots tape

theorem upperReadRecord_reconstruct (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots) :
    OriginalWholeCut.reconstructRecord rows repeats p slots
        (upperReadRecord rows repeats p r chosen q slots tape) =
      WholeArraySampler.evaluate rows repeats (p.append (r.append (.step chosen q))) slots tape := by
  cases r with
  | refl => exact OriginalWholeCut.reconstruct_original rows repeats p chosen q slots tape
  | step upperChild tail =>
      exact OriginalWholeCut.reconstruct_original rows repeats p upperChild
        (tail.append (.step chosen q)) slots tape

theorem ownValues_readRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1)) :
    ∀ (chosen : Fin (branch j)) (q : Path branch j k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots),
      OriginalCutBucketReplacement.ownValues rows repeats p slots
          (OriginalWholeCut.readRecord rows repeats p chosen q slots tape).2.1 =
        fun direction => RecursiveSampler.evaluate F2 repeats (.step chosen q)
          (LeafDomain (cutSlots p slots))
          ((WholeArraySubtreeSplit.extract rows repeats p (.step chosen q) slots tape)
            (.inl ()) direction) := by
  induction n generalizing j with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro chosen q slots tape; rfl
      | step child p =>
          intro chosen q slots tape
          exact ih p chosen q (childSlots slots child) (tape (.inr (.inl ())))

theorem upperReadRecord_ownValues (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots) :
    OriginalCutBucketReplacement.ownValues rows repeats p slots
        (upperReadRecord rows repeats p r chosen q slots tape).2.1 =
      fun direction => RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots))
        (UpperScalarCutBucket.continuedRootTape rows repeats r chosen q (cutSlots p slots)
          (WholeArraySubtreeSplit.extract rows repeats p (r.append (.step chosen q)) slots tape)
          direction) := by
  cases r with
  | refl => exact ownValues_readRecord rows repeats p chosen q slots tape
  | step upperChild tail =>
      exact ownValues_readRecord rows repeats p upperChild (tail.append (.step chosen q)) slots tape

def upperPairRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p) :=
  OriginalCutCollision.pairRecord rows repeats p slots
    (a, (OriginalWholeCutBridge.numberRecord rows repeats p slots
      (upperReadRecord rows repeats p r chosen q slots tape), fresh))

private theorem originalPairRecord_numberRecord (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats p slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    OriginalCutCollision.pairRecord rows repeats p slots
        (a, (OriginalWholeCutBridge.numberRecord rows repeats p slots record, fresh)) =
      HierarchicalAgreementMean.pairRecord slots (upperNode p)
        (HierarchicalMatrixTable.backgroundOf slots (upperNode p)
          (OriginalWholeCut.reconstructRecord rows repeats p slots record),
          CutNodeRows.bucketSampleEquiv rows p slots
            (a, (OriginalCutBucketReplacement.ownValues rows repeats p slots record.2.1, fresh))) := by
  simpa only [OriginalCutPairLaw.transportPair, OriginalCutBucketLaw.read,
    OriginalCutCollision.oldArrays, OriginalCutBucketLaw.oldRecord_numberRecord] using
      OriginalCutPairLaw.pairRecord_eq rows repeats p slots
        (a, (OriginalWholeCutBridge.numberRecord rows repeats p slots record, fresh))

theorem upperBuckets_eq_ownValues (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots) :
    UpperScalarCutBucket.upperBuckets rows repeats p r slots
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) =
      OriginalCutBucketReplacement.ownValues rows repeats p slots
        (upperReadRecord rows repeats p r chosen q slots
          (assocTapeEquiv rows repeats p r (.step chosen q) slots tape)).2.1 := by
  rw [UpperScalarCutBucket.upperBuckets_readRecord, upperReadRecord_ownValues,
    extract_assocTapeEquiv]

theorem pairRecord_read_eq_upper (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    UpperScalarCutBucket.pairRecord rows repeats p r slots
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) a fresh =
      upperPairRecord rows repeats p r chosen q slots
        (assocTapeEquiv rows repeats p r (.step chosen q) slots tape) a fresh := by
  have harrays :
      OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots
          (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) =
        OriginalWholeCut.reconstructRecord rows repeats p slots
          (upperReadRecord rows repeats p r chosen q slots
            (assocTapeEquiv rows repeats p r (.step chosen q) slots tape)) := by
    rw [OriginalWholeCut.reconstruct_original, upperReadRecord_reconstruct,
      evaluate_assocTapeEquiv]
  rw [UpperScalarCutBucket.pairRecord_eq]
  unfold upperPairRecord
  rw [originalPairRecord_numberRecord, harrays, upperBuckets_eq_ownValues]

theorem enlargedPairRecord_read_eq_upper (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (a : BucketSampler.Direction (rows (j + 1)))
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    UpperScalarCutBucket.enlargedPairRecord rows repeats p r slots
        (a, UpperScalarCutReconstruction.read rows repeats p r chosen q slots tapes) =
      upperPairRecord rows repeats p r chosen q slots
        (assocTapeEquiv rows repeats p r (.step chosen q) slots tapes.1) a
        (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)) tapes.2) := by
  rw [UpperScalarCutBucket.enlargedPairRecord_read]
  exact pairRecord_read_eq_upper rows repeats p r chosen q slots tapes.1 a _

theorem numberedPairRecord_read_eq_upper (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (a : BucketSampler.Direction (rows (j + 1)))
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    UpperScalarCutBucket.numberedPairRecord rows repeats p r slots
        (a, UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots
          (UpperScalarCutReconstruction.read rows repeats p r chosen q slots tapes)) =
      upperPairRecord rows repeats p r chosen q slots
        (assocTapeEquiv rows repeats p r (.step chosen q) slots tapes.1) a
        (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)) tapes.2) := by
  rw [UpperScalarCutBucket.numberedPairRecord_numberRecord]
  exact enlargedPairRecord_read_eq_upper rows repeats p r chosen q slots a tapes

end
end PerfectCompleteness.UpperScalarCutErasure

end

end OAI
