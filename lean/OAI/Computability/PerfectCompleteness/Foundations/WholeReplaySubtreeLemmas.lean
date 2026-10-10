import OAI.Computability.PerfectCompleteness.Foundations.WholeArraySubtreeSplit
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutReplayLemmas
import OAI.Computability.PerfectCompleteness.Machines.OwnInputReferenceLemmas
import OAI.Computability.PerfectCompleteness.Machines.WholeArrayInteriorOwnInputLaw

namespace OAI

section

namespace PerfectCompleteness.WholeReplaySubtree

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit

noncomputable section

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n k m t : Nat}

def extract (rows repeats : Nat → Nat) :
    {n k m : Nat} → (pUp : Path branch n k) → (pDown : Path branch k (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) →
      WholeCutReplay.Tape rows repeats (pUp.append pDown) slots clean →
        WholeCutReplay.Tape rows repeats pDown (subtreeSlots pUp slots) clean
  | _, _, _, .refl _, _, _, _, tape => tape
  | _, _, _, .step i pUp, pDown, slots, clean, tape =>
      extract rows repeats pUp pDown (childSlots slots i) clean tape.2.1

@[simp] theorem extract_refl (rows repeats : Nat → Nat) (pDown : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (tape : WholeCutReplay.Tape rows repeats pDown slots clean) :
    extract rows repeats (.refl n) pDown slots clean tape = tape := by
  cases pDown <;> rfl

@[simp] theorem extract_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (pUp : Path branch n k) (pDown : Path branch k (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (tape : WholeCutReplay.Tape rows repeats ((Path.step i pUp).append pDown) slots clean) :
    extract rows repeats (.step i pUp) pDown slots clean tape =
      extract rows repeats pUp pDown (childSlots slots i) clean tape.2.1 := rfl

theorem restrictArrays_evaluateArrays (rows repeats : Nat → Nat) (pUp : Path branch n k) :
    ∀ {m : Nat} (pDown : Path branch k (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
      (tape : WholeCutReplay.Tape rows repeats (pUp.append pDown) slots clean),
      restrictArrays rows pUp slots
          (WholeCutReplay.evaluateArrays rows repeats (pUp.append pDown) slots clean tape) =
        WholeCutReplay.evaluateArrays rows repeats pDown (subtreeSlots pUp slots) clean
          (extract rows repeats pUp pDown slots clean tape) := by
  induction pUp with
  | refl n =>
      intro m pDown slots clean tape
      cases pDown <;> rfl
  | step i pUp ih =>
      intro m pDown slots clean tape
      have hselected := funext (WholeCutReplay.evaluateArrays_step_selected rows repeats i
        (pUp.append pDown) slots clean tape)
      exact (congrArg (restrictArrays rows pUp (childSlots slots i)) hselected).trans
        (ih pDown (childSlots slots i) clean tape.2.1)

def restrictBlocks (rows : Nat → Nat) :
    {n k : Nat} → Path branch n k →
      ((node : Nodes branch n) → Block rows node) → (node : Nodes branch k) → Block rows node
  | _, _, .refl _, blocks => blocks
  | _, _, .step i pUp, blocks =>
      restrictBlocks rows pUp (fun node => blocks (.inr (i, node)))

theorem restrictBlocks_joint (rows : Nat → Nat) (pUp : Path branch n k) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (arrays : Arrays slots rows) (x : Domain slots),
      restrictBlocks rows pUp (joint arrays x) =
        joint (restrictArrays rows pUp slots arrays) (pUp.restriction (LeafDomain slots) x) := by
  induction pUp with
  | refl n =>
      intro slots arrays x
      rfl
  | step i pUp ih =>
      intro slots arrays x
      exact ih (childSlots slots i) (fun node => arrays (.inr (i, node)))
        (restrictChild slots i x)

theorem evaluate_extract (rows repeats : Nat → Nat)
    (pUp : Path branch n k) (pDown : Path branch k (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (tape : WholeCutReplay.Tape rows repeats (pUp.append pDown) slots clean) (x : Domain slots) :
    restrictBlocks rows pUp
        (WholeCutReplay.evaluate rows repeats (pUp.append pDown) slots clean tape x) =
      WholeCutReplay.evaluate rows repeats pDown (subtreeSlots pUp slots) clean
        (extract rows repeats pUp pDown slots clean tape) (pUp.restriction (LeafDomain slots) x) := by
  calc
    _ = restrictBlocks rows pUp
        (joint (WholeCutReplay.evaluateArrays rows repeats (pUp.append pDown) slots clean tape) x) :=
      congrArg (restrictBlocks rows pUp)
        (WholeCutReplay.joint_evaluateArrays_apply rows repeats (pUp.append pDown)
          slots clean tape x).symm
    _ = joint (restrictArrays rows pUp slots
        (WholeCutReplay.evaluateArrays rows repeats (pUp.append pDown) slots clean tape))
          (pUp.restriction (LeafDomain slots) x) :=
      restrictBlocks_joint rows pUp slots _ x
    _ = joint (WholeCutReplay.evaluateArrays rows repeats pDown (subtreeSlots pUp slots) clean
        (extract rows repeats pUp pDown slots clean tape))
          (pUp.restriction (LeafDomain slots) x) :=
      congrArg (fun arrays => joint arrays (pUp.restriction (LeafDomain slots) x))
        (restrictArrays_evaluateArrays rows repeats pUp pDown slots clean tape)
    _ = _ := WholeCutReplay.joint_evaluateArrays_apply rows repeats pDown
      (subtreeSlots pUp slots) clean (extract rows repeats pUp pDown slots clean tape)
      (pUp.restriction (LeafDomain slots) x)

def rootBuckets (rows repeats : Nat → Nat) :
    {k m : Nat} → (pDown : Path branch k (m + 1)) → m + 1 < k →
      (slots : Slots branch k → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → WholeCutReplay.Tape rows repeats pDown slots clean →
        BucketSampler.Direction (rows k) → H slots
  | _, _, .refl _, hproper, _, _, _, _ => False.elim ((Nat.lt_irrefl _) hproper)
  | _, _, .step i pDown, _, slots, clean, tape, bucket =>
      WholeCutReplay.bucketSpace rows repeats i pDown slots clean tape bucket

@[simp] theorem rootBuckets_step (rows repeats : Nat → Nat) (i : Fin (branch k))
    (pDown : Path branch k (m + 1)) (hproper : m + 1 < k + 1)
    (slots : Slots branch (k + 1) → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (tape : WholeCutReplay.Tape rows repeats (.step i pDown) slots clean)
    (bucket : BucketSampler.Direction (rows (k + 1))) :
    rootBuckets rows repeats (.step i pDown) hproper slots clean tape bucket =
      WholeCutReplay.bucketSpace rows repeats i pDown slots clean tape bucket := rfl

def buckets (rows repeats : Nat → Nat)
    (pUp : Path branch n k) (pDown : Path branch k (m + 1)) (hproper : m + 1 < k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (tape : WholeCutReplay.Tape rows repeats (pUp.append pDown) slots clean) :
    BucketSampler.Direction (rows k) → H (subtreeSlots pUp slots) :=
  rootBuckets rows repeats pDown hproper (subtreeSlots pUp slots) clean
    (extract rows repeats pUp pDown slots clean tape)

def knownBuckets (rows repeats : Nat → Nat)
    (pUp : Path branch n k) (pDown : Path branch k (m + 1)) (hproper : m + 1 < k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop)
    (W : Submodule F2 (Fin (rows k) → F2))
    (tape : WholeCutReplay.Tape rows repeats (pUp.append pDown) slots clean) :
    HiddenBucketBias.VisibleDirection W → H (subtreeSlots pUp slots) :=
  fun v => buckets rows repeats pUp pDown hproper slots clean tape v.val

def knownBucketsAtNode (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1)) (hproper : m + 1 < Nodes.height upper)
    (clean : Fin (branch m) → Prop) (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutReplay.Tape rows repeats ((Nodes.path upper).append pDown) slots clean) :
    HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper :=
  knownBuckets rows repeats (Nodes.path upper) pDown hproper slots clean W tape

@[simp] theorem knownBucketsAtNode_apply (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1)) (hproper : m + 1 < Nodes.height upper)
    (clean : Fin (branch m) → Prop) (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutReplay.Tape rows repeats ((Nodes.path upper).append pDown) slots clean)
    (v : HiddenBucketBias.VisibleDirection W) :
    knownBucketsAtNode rows repeats slots upper pDown hproper clean W tape v =
      rootBuckets rows repeats pDown hproper (nodeSlots slots upper) clean
        (extract rows repeats (Nodes.path upper) pDown slots clean tape) v.val := rfl

end
end PerfectCompleteness.WholeReplaySubtree

end

section

namespace PerfectCompleteness.WholeCutSubtree

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n k m t : Nat}

def extract (rows repeats : Nat → Nat) :
    {n k m : Nat} → (pUp : Path branch n k) → (pDown : Path branch k m) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      WholeCutSampler.Tape rows repeats (pUp.append pDown) slots →
        WholeCutSampler.Tape rows repeats pDown (subtreeSlots pUp slots)
  | _, _, _, .refl _, _, _, tape => tape
  | _, _, _, .step i pUp, pDown, slots, tape =>
      extract rows repeats pUp pDown (childSlots slots i) tape.2.1

@[simp] theorem extract_refl (rows repeats : Nat → Nat) (pDown : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats pDown slots) :
    extract rows repeats (.refl n) pDown slots tape = tape := rfl

@[simp] theorem extract_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (pUp : Path branch n k) (pDown : Path branch k m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats ((Path.step i pUp).append pDown) slots) :
    extract rows repeats (.step i pUp) pDown slots tape =
      extract rows repeats pUp pDown (childSlots slots i) tape.2.1 := rfl

theorem erase_extract (rows repeats : Nat → Nat) (pUp : Path branch n k) :
    ∀ {m : Nat} (pDown : Path branch k (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (tape : WholeCutSampler.Tape rows repeats (pUp.append pDown) slots),
      WholeReplaySubtree.extract rows repeats pUp pDown slots clean
          (WholeCutReplay.erase rows repeats (pUp.append pDown) slots clean tape) =
        WholeCutReplay.erase rows repeats pDown (subtreeSlots pUp slots) clean
          (extract rows repeats pUp pDown slots tape) := by
  induction pUp with
  | refl n =>
      intro m pDown slots clean tape
      cases pDown <;> rfl
  | step i pUp ih =>
      intro m pDown slots clean tape
      exact ih pDown (childSlots slots i) clean tape.2.1

theorem zero_extract (rows repeats : Nat → Nat) (pUp : Path branch n k) :
    ∀ {m : Nat} (pDown : Path branch k (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (tape : WholeCutSampler.Tape rows repeats (pUp.append pDown) slots),
      WholeCutZero.ZeroAtClean rows repeats (pUp.append pDown) slots clean tape →
        WholeCutZero.ZeroAtClean rows repeats pDown (subtreeSlots pUp slots) clean
          (extract rows repeats pUp pDown slots tape) := by
  induction pUp with
  | refl n => intros; assumption
  | step i pUp ih =>
      intro m pDown slots clean tape hzero
      exact ih pDown (childSlots slots i) clean tape.2.1 hzero.2

theorem collapse_extract (rows repeats : Nat → Nat) (pUp : Path branch n k) :
    ∀ {m : Nat} (pDown : Path branch k m)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeCutSampler.Tape rows repeats (pUp.append pDown) slots),
      WholeCutSampler.collapse rows repeats pDown (subtreeSlots pUp slots)
          (extract rows repeats pUp pDown slots tape) =
        WholeArraySubtreeSplit.extract rows repeats pUp pDown slots
          (WholeCutSampler.collapse rows repeats (pUp.append pDown) slots tape) := by
  induction pUp with
  | refl n => intros; rfl
  | step i pUp ih =>
      intro m pDown slots tape
      exact ih pDown (childSlots slots i) tape.2.1

def rootBuckets (rows repeats : Nat → Nat) :
    {k m : Nat} → (pDown : Path branch k m) → m < k →
      (slots : Slots branch k → Fin t → MixedSupport.Slot) →
      WholeCutSampler.Tape rows repeats pDown slots →
        BucketSampler.Direction (rows k) → H slots
  | _, _, .refl _, hproper, _, _, _ => False.elim ((Nat.lt_irrefl _) hproper)
  | _, _, .step i pDown, _, slots, tape, bucket =>
      CutSamplerRefinement.evaluate F2 repeats (.step i pDown) (LeafDomain slots)
        (tape.1 bucket)

def knownBuckets (rows repeats : Nat → Nat)
    (pUp : Path branch n k) (pDown : Path branch k m) (hproper : m < k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows k) → F2))
    (tape : WholeCutSampler.Tape rows repeats (pUp.append pDown) slots) :
    HiddenBucketBias.VisibleDirection W → H (subtreeSlots pUp slots) :=
  fun v => rootBuckets rows repeats pDown hproper (subtreeSlots pUp slots)
    (extract rows repeats pUp pDown slots tape) v.val

theorem rootBuckets_erase (rows repeats : Nat → Nat)
    (pDown : Path branch k (m + 1)) (hproper : m + 1 < k)
    (slots : Slots branch k → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : WholeCutSampler.Tape rows repeats pDown slots)
    (hzero : WholeCutZero.ZeroAtClean rows repeats pDown slots clean tape) :
    WholeReplaySubtree.rootBuckets rows repeats pDown hproper slots clean
        (WholeCutReplay.erase rows repeats pDown slots clean tape) =
      rootBuckets rows repeats pDown hproper slots tape := by
  cases pDown with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i pDown =>
      funext bucket
      exact WholeCutReplay.bucketSpace_erase rows repeats i pDown slots clean tape hzero bucket

theorem knownBuckets_erase (rows repeats : Nat → Nat)
    (pUp : Path branch n k) (pDown : Path branch k (m + 1)) (hproper : m + 1 < k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (W : Submodule F2 (Fin (rows k) → F2))
    (tape : WholeCutSampler.Tape rows repeats (pUp.append pDown) slots)
    (hzero : WholeCutZero.ZeroAtClean rows repeats (pUp.append pDown) slots clean tape) :
    WholeReplaySubtree.knownBuckets rows repeats pUp pDown hproper slots clean W
        (WholeCutReplay.erase rows repeats (pUp.append pDown) slots clean tape) =
      knownBuckets rows repeats pUp pDown hproper slots W tape := by
  funext v
  unfold WholeReplaySubtree.knownBuckets WholeReplaySubtree.buckets knownBuckets
  rw [erase_extract, rootBuckets_erase rows repeats pDown hproper
    (subtreeSlots pUp slots) clean (extract rows repeats pUp pDown slots tape)
    (zero_extract rows repeats pUp pDown slots clean tape hzero)]

theorem knownBuckets_eq_original (rows repeats : Nat → Nat)
    (pUp : Path branch n k) (pDown : Path branch k m) (hproper : m < k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows k) → F2))
    (tape : WholeCutSampler.Tape rows repeats (pUp.append pDown) slots) :
    knownBuckets rows repeats pUp pDown hproper slots W tape =
      fun v => RecursiveSampler.evaluate F2 repeats pDown (LeafDomain (subtreeSlots pUp slots))
        ((WholeArrayPositiveSplit.split rows repeats pUp pDown hproper slots W
          (WholeCutSampler.collapse rows repeats (pUp.append pDown) slots tape)).2.1 v) := by
  cases pDown with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i pDown =>
      funext v
      change CutSamplerRefinement.evaluate F2 repeats (.step i pDown)
          (LeafDomain (subtreeSlots pUp slots))
          ((extract rows repeats pUp (.step i pDown) slots tape).1 v.val) =
        RecursiveSampler.evaluate F2 repeats (.step i pDown)
          (LeafDomain (subtreeSlots pUp slots))
          ((WholeArraySubtreeSplit.extract rows repeats pUp (.step i pDown) slots
            (WholeCutSampler.collapse rows repeats (pUp.append (.step i pDown)) slots tape))
              (.inl ()) v.val)
      rw [← collapse_extract]
      rfl

def knownBucketsAtNode (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) m) (hproper : m < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutSampler.Tape rows repeats ((Nodes.path upper).append pDown) slots) :
    HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper :=
  knownBuckets rows repeats (Nodes.path upper) pDown hproper slots W tape

theorem knownBucketsAtNode_erase (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1)) (hproper : m + 1 < Nodes.height upper)
    (clean : Fin (branch m) → Prop)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutSampler.Tape rows repeats ((Nodes.path upper).append pDown) slots)
    (hzero : WholeCutZero.ZeroAtClean rows repeats ((Nodes.path upper).append pDown)
      slots clean tape) :
    WholeReplaySubtree.knownBucketsAtNode rows repeats slots upper pDown hproper clean W
        (WholeCutReplay.erase rows repeats ((Nodes.path upper).append pDown) slots clean tape) =
      knownBucketsAtNode rows repeats slots upper pDown hproper W tape :=
  knownBuckets_erase rows repeats (Nodes.path upper) pDown hproper slots clean W tape hzero

theorem knownBucketsAtNode_eq_ownInput (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (a : OwnInputReference.LowerVector rows lower)
    (tape : WholeCutSampler.Tape rows repeats ((Nodes.path upper).append cut.path) slots) :
    knownBucketsAtNode rows repeats slots upper cut.path cut.proper W tape =
      (WholeArrayInteriorOwnInputLaw.ownInput rows repeats slots upper lower cut W a
        (WholeCutSampler.collapse rows repeats ((Nodes.path upper).append cut.path) slots tape)).knownBuckets :=
  knownBuckets_eq_original rows repeats (Nodes.path upper) cut.path cut.proper slots W tape

end
end PerfectCompleteness.WholeCutSubtree

end

end OAI
