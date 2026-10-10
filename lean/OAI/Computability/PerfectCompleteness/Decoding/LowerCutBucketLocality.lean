import OAI.Computability.PerfectCompleteness.Decoding.LowerCutRowsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutReplayLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeReplaySubtreeLemmas

namespace OAI

section

namespace PerfectCompleteness.LowerCutBucketLocality

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping WholeArraySubtreeSplit

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n k m t : Nat}

def rootBuckets (rows repeats : Nat → Nat) :
    {k m : Nat} → (pDown : Path branch k (m + 1)) → m + 1 < k →
      (slots : Slots branch k → Fin t → MixedSupport.Slot) →
      Exterior rows repeats pDown slots →
      LowerCutCallSplit.Assembled rows repeats pDown slots →
        BucketSampler.Direction (rows k) → H slots
  | _, _, .refl _, hproper, _, _, _, _ => False.elim ((Nat.lt_irrefl _) hproper)
  | _, _, .step i pDown, _, slots, exterior, assembled, direction =>
      LowerCutScalar.reconstruct F2 repeats (.step i pDown) (LeafDomain slots)
        (fun terminal => assembled.1 (.inl (direction, terminal))) (exterior.1 direction)

def buckets (rows repeats : Nat → Nat) :
    {n k m : Nat} → (pUp : Path branch n k) → (pDown : Path branch k (m + 1)) →
      m + 1 < k → (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      Exterior rows repeats (pUp.append pDown) slots →
      LowerCutCallSplit.Assembled rows repeats (pUp.append pDown) slots →
        BucketSampler.Direction (rows k) → H (subtreeSlots pUp slots)
  | _, _, _, .refl _, pDown, hproper, slots, exterior, assembled =>
      rootBuckets rows repeats pDown hproper slots exterior assembled
  | _, _, _, .step i pUp, pDown, hproper, slots, exterior, assembled =>
      buckets rows repeats pUp pDown hproper (childSlots slots i) exterior.2.1
        (fun call => assembled.1 (.inr call), assembled.2)

theorem buckets_congr_otherCalls (rows repeats : Nat → Nat) (pUp : Path branch n k) :
    ∀ {m : Nat} (pDown : Path branch k (m + 1)) (hproper : m + 1 < k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (exterior : Exterior rows repeats (pUp.append pDown) slots)
      (x y : LowerCutCallSplit.Assembled rows repeats (pUp.append pDown) slots),
      (∀ call, (∀ row, call ≠ WholeCutCalls.directRow rows repeats (pUp.append pDown) row) →
        y.1 call = x.1 call) →
      buckets rows repeats pUp pDown hproper slots exterior y =
        buckets rows repeats pUp pDown hproper slots exterior x := by
  induction pUp with
  | refl k =>
      intro m pDown hproper slots exterior x y hcalls
      cases pDown with
      | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
      | step i pDown =>
          funext direction
          have hvalues :
              ((fun terminal => y.1 (.inl (direction, terminal))) :
                LowerCutScalar.Values F2 repeats (.step i pDown) (LeafDomain slots)) =
              (fun terminal => x.1 (.inl (direction, terminal))) := by
            funext terminal
            apply hcalls (.inl (direction, terminal))
            intro row h
            cases h
          simp only [buckets, rootBuckets]
          rw [hvalues]
  | step i pUp ih =>
      intro m pDown hproper slots exterior x y hcalls
      apply ih pDown hproper (childSlots slots i) exterior.2.1
        (fun call => x.1 (.inr call), x.2) (fun call => y.1 (.inr call), y.2)
      intro call hcall
      apply hcalls (.inr call)
      intro row h
      exact hcall row (Sum.inr.inj h)

theorem buckets_splitTape (rows repeats : Nat → Nat) (pUp : Path branch n k) :
    ∀ {m : Nat} (pDown : Path branch k (m + 1)) (hproper : m + 1 < k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeCutSampler.Tape rows repeats (pUp.append pDown) slots),
      buckets rows repeats pUp pDown hproper slots
          (splitTape rows repeats (pUp.append pDown) slots tape).1
          (CutChildGrouping.assemble (cutSlots (pUp.append pDown) slots) rows
            (splitTape rows repeats (pUp.append pDown) slots tape).2) =
        WholeCutSubtree.rootBuckets rows repeats pDown hproper (subtreeSlots pUp slots)
          (WholeCutSubtree.extract rows repeats pUp pDown slots tape) := by
  induction pUp with
  | refl k =>
      intro m pDown hproper slots tape
      cases pDown with
      | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
      | step i pDown =>
          funext direction
          exact LowerCutScalar.reconstruct_splitTape F2 repeats (.step i pDown)
            (LeafDomain slots) (tape.1 direction)
  | step i pUp ih =>
      intro m pDown hproper slots tape
      exact ih pDown hproper (childSlots slots i) tape.2.1

def knownBuckets (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (exterior : Exterior rows repeats ((Nodes.path upper).append pDown) slots)
    (assembled : LowerCutCallSplit.Assembled rows repeats ((Nodes.path upper).append pDown) slots) :
    HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper :=
  fun v => buckets rows repeats (Nodes.path upper) pDown hproper slots exterior assembled v.val

def knownBucketsOfComplement (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (exterior : Exterior rows repeats ((Nodes.path upper).append pDown) slots)
    (complement : LowerCutCallSplit.Complement rows repeats ((Nodes.path upper).append pDown) slots) :
    HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper :=
  knownBuckets rows repeats slots upper pDown hproper W exterior
    (LowerCutCallSplit.merge rows repeats ((Nodes.path upper).append pDown) slots complement 0)

theorem knownBuckets_merge (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (exterior : Exterior rows repeats ((Nodes.path upper).append pDown) slots)
    (complement : LowerCutCallSplit.Complement rows repeats ((Nodes.path upper).append pDown) slots)
    (fresh : LowerCutCallSplit.NativeRows rows ((Nodes.path upper).append pDown) slots) :
    knownBuckets rows repeats slots upper pDown hproper W exterior
        (LowerCutCallSplit.merge rows repeats ((Nodes.path upper).append pDown) slots complement fresh) =
      knownBucketsOfComplement rows repeats slots upper pDown hproper W exterior complement := by
  have h := buckets_congr_otherCalls rows repeats (Nodes.path upper) pDown hproper slots exterior
    (LowerCutCallSplit.merge rows repeats ((Nodes.path upper).append pDown) slots complement 0)
    (LowerCutCallSplit.merge rows repeats ((Nodes.path upper).append pDown) slots complement fresh)
    (fun call hcall =>
      (LowerCutCallSplit.merge_otherCall rows repeats ((Nodes.path upper).append pDown) slots
        complement fresh ⟨call, hcall⟩).trans
      (LowerCutCallSplit.merge_otherCall rows repeats ((Nodes.path upper).append pDown) slots
        complement 0 ⟨call, hcall⟩).symm)
  funext v
  exact congrFun h v.val

theorem knownBuckets_eq_complement (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (exterior : Exterior rows repeats ((Nodes.path upper).append pDown) slots)
    (assembled : LowerCutCallSplit.Assembled rows repeats ((Nodes.path upper).append pDown) slots) :
    knownBuckets rows repeats slots upper pDown hproper W exterior assembled =
      knownBucketsOfComplement rows repeats slots upper pDown hproper W exterior
        (LowerCutCallSplit.complement rows repeats ((Nodes.path upper).append pDown) slots assembled) := by
  have h := buckets_congr_otherCalls rows repeats (Nodes.path upper) pDown hproper slots exterior
    (LowerCutCallSplit.merge rows repeats ((Nodes.path upper).append pDown) slots
      (LowerCutCallSplit.complement rows repeats ((Nodes.path upper).append pDown) slots assembled) 0)
    assembled (fun call hcall =>
      (LowerCutCallSplit.merge_otherCall rows repeats ((Nodes.path upper).append pDown) slots
        (LowerCutCallSplit.complement rows repeats ((Nodes.path upper).append pDown) slots assembled)
        0 ⟨call, hcall⟩).symm)
  funext v
  exact congrFun h v.val

theorem knownBucketsAtNode_eq_complement (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutSampler.Tape rows repeats ((Nodes.path upper).append pDown) slots) :
    WholeCutSubtree.knownBucketsAtNode rows repeats slots upper pDown hproper W tape =
      knownBucketsOfComplement rows repeats slots upper pDown hproper W
        (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).1
        (LowerCutCallSplit.complement rows repeats ((Nodes.path upper).append pDown) slots
          (CutChildGrouping.assemble (cutSlots ((Nodes.path upper).append pDown) slots) rows
            (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).2)) := by
  have hreader := buckets_splitTape rows repeats (Nodes.path upper) pDown hproper slots tape
  have hknown : WholeCutSubtree.knownBucketsAtNode rows repeats slots upper pDown hproper W tape =
      knownBuckets rows repeats slots upper pDown hproper W
        (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).1
        (CutChildGrouping.assemble (cutSlots ((Nodes.path upper).append pDown) slots) rows
          (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).2) := by
    funext v
    exact (congrFun hreader v.val).symm
  exact hknown.trans (knownBuckets_eq_complement rows repeats slots upper pDown hproper W _ _)

theorem knownBucketsAtNode_join (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (exterior : Exterior rows repeats ((Nodes.path upper).append pDown) slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats ((Nodes.path upper).append pDown))
      (cutSlots ((Nodes.path upper).append pDown) slots) rows) :
    WholeCutSubtree.knownBucketsAtNode rows repeats slots upper pDown hproper W
        ((splitTape rows repeats ((Nodes.path upper).append pDown) slots).symm (exterior, raw)) =
      knownBucketsOfComplement rows repeats slots upper pDown hproper W exterior
        (LowerCutCallSplit.complement rows repeats ((Nodes.path upper).append pDown) slots
          (CutChildGrouping.assemble (cutSlots ((Nodes.path upper).append pDown) slots) rows raw)) := by
  have h := knownBucketsAtNode_eq_complement rows repeats slots upper pDown hproper W
    ((splitTape rows repeats ((Nodes.path upper).append pDown) slots).symm (exterior, raw))
  rw [Equiv.apply_symm_apply] at h
  exact h

theorem knownBucketsAtNode_erase_eq (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper) (clean : Fin (branch m) → Prop)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutSampler.Tape rows repeats ((Nodes.path upper).append pDown) slots)
    (hzero : WholeCutZero.ZeroAtClean rows repeats ((Nodes.path upper).append pDown) slots clean tape) :
    WholeReplaySubtree.knownBucketsAtNode rows repeats slots upper pDown hproper clean W
        (WholeCutReplay.erase rows repeats ((Nodes.path upper).append pDown) slots clean tape) =
      knownBucketsOfComplement rows repeats slots upper pDown hproper W
        (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).1
        (LowerCutCallSplit.complement rows repeats ((Nodes.path upper).append pDown) slots
          (CutChildGrouping.assemble (cutSlots ((Nodes.path upper).append pDown) slots) rows
            (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).2)) :=
  (WholeCutSubtree.knownBucketsAtNode_erase rows repeats slots upper pDown hproper clean W tape hzero).trans
    (knownBucketsAtNode_eq_complement rows repeats slots upper pDown hproper W tape)

theorem knownBucketsAtNode_assemble_splitTape (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper) (clean : Fin (branch m) → Prop)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutSampler.Tape rows repeats ((Nodes.path upper).append pDown) slots)
    (hzero : WholeCutZero.ZeroAtClean rows repeats ((Nodes.path upper).append pDown) slots clean tape) :
    WholeReplaySubtree.knownBucketsAtNode rows repeats slots upper pDown hproper clean W
        (WholeCutReplayGrouping.assemble rows repeats ((Nodes.path upper).append pDown) slots clean
          (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).1
          (fun child => (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).2 child.val)) =
      knownBucketsOfComplement rows repeats slots upper pDown hproper W
        (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).1
        (LowerCutCallSplit.complement rows repeats ((Nodes.path upper).append pDown) slots
          (CutChildGrouping.assemble (cutSlots ((Nodes.path upper).append pDown) slots) rows
            (splitTape rows repeats ((Nodes.path upper).append pDown) slots tape).2)) := by
  exact (congrArg (WholeReplaySubtree.knownBucketsAtNode rows repeats slots upper pDown hproper clean W)
    (WholeCutReplayGrouping.assemble_splitTape rows repeats ((Nodes.path upper).append pDown)
      slots clean tape)).trans
    (knownBucketsAtNode_erase_eq rows repeats slots upper pDown hproper clean W tape hzero)

theorem knownBucketsAtNode_assemble (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper) (clean : Fin (branch m) → Prop)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (exterior : Exterior rows repeats ((Nodes.path upper).append pDown) slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats ((Nodes.path upper).append pDown))
      (cutSlots ((Nodes.path upper).append pDown) slots) rows)
    (hzero : WholeCutZero.ZeroAtClean rows repeats ((Nodes.path upper).append pDown) slots clean
      ((splitTape rows repeats ((Nodes.path upper).append pDown) slots).symm (exterior, raw))) :
    WholeReplaySubtree.knownBucketsAtNode rows repeats slots upper pDown hproper clean W
        (WholeCutReplayGrouping.assemble rows repeats ((Nodes.path upper).append pDown) slots clean
          exterior (fun child => raw child.val)) =
      knownBucketsOfComplement rows repeats slots upper pDown hproper W exterior
        (LowerCutCallSplit.complement rows repeats ((Nodes.path upper).append pDown) slots
          (CutChildGrouping.assemble (cutSlots ((Nodes.path upper).append pDown) slots) rows raw)) := by
  have h := knownBucketsAtNode_assemble_splitTape rows repeats slots upper pDown hproper clean W
    ((splitTape rows repeats ((Nodes.path upper).append pDown) slots).symm (exterior, raw)) hzero
  rw [Equiv.apply_symm_apply] at h
  exact h

end
end PerfectCompleteness.LowerCutBucketLocality

end

end OAI
