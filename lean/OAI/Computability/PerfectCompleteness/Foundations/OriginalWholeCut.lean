import OAI.Computability.PerfectCompleteness.Foundations.OriginalTerminalSplitLemmas
import OAI.Computability.PerfectCompleteness.Machines.OriginalWholeCutTape

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

abbrev Values (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalCutCalls.Index rows repeats p → H (cutSlots p slots)

abbrev ChildArrays (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :=
  (child : Fin (branch m)) → Arrays (childSlots slots child) rows

abbrev BelowArrays (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  ChildArrays rows (cutSlots p slots)

abbrev Record (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p slots × (Values rows repeats p slots × BelowArrays rows p slots)

def belowEvaluate (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (ω : BelowTape rows repeats chosen q slots) : ChildArrays rows slots :=
  WholeArraySampler.childrenAt slots rows chosen
    (WholeArraySampler.evaluate rows repeats q (childSlots slots chosen) ω.1) ω.2

def reconstructBuckets (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (values : BucketSampler.Direction (rows n) →
      OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain slots))
    (exterior : BucketSampler.Direction (rows n) →
      OriginalTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots)) :
    Fin (rows n) → H slots :=
  BucketSampler.evaluate (rows n) id (fun direction =>
    OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain slots)
      (values direction) (exterior direction))

theorem reconstructBuckets_original (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (r : Path branch (m + 1) k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.RootTape rows repeats (p.append r) slots) :
    reconstructBuckets rows repeats p slots
        (fun direction terminal => RecursiveSampler.evaluate F2 repeats r
          (p.family (LeafDomain slots))
          ((OriginalTerminalSplit.splitTape F2 repeats p r (LeafDomain slots)
            (ω direction)).1 terminal))
        (fun direction => (OriginalTerminalSplit.splitTape F2 repeats p r (LeafDomain slots)
          (ω direction)).2) =
      BucketSampler.recursiveEvaluate (rows n) repeats (p.append r) (LeafDomain slots) ω := by
  have h := funext (fun direction : BucketSampler.Direction (rows n) =>
    OriginalScalarReconstruction.reconstruct_original F2 repeats p (LeafDomain slots) r
      (ω direction))
  exact congrArg (BucketSampler.evaluate (rows n) (id : H slots → H slots)) h

def reconstruct (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Exterior rows repeats p slots → Values rows repeats p slots →
          BelowArrays rows p slots → Arrays slots rows
  | _, m, .refl _, slots, _, values, below =>
      WholeArraySampler.assemble slots rows
        (BucketSampler.evaluate (rows (m + 1)) (id : H slots → H slots) values) below
  | _, _, .step i p, slots, exterior, values, below =>
      WholeArraySampler.assemble slots rows
        (reconstructBuckets rows repeats (.step i p) slots
          (fun direction terminal => values (.inl (direction, terminal))) exterior.1)
        (WholeArraySampler.childrenAt slots rows i
          (reconstruct rows repeats p (childSlots slots i) exterior.2.1
            (fun call => values (.inr call)) below) exterior.2.2)

def reconstructRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) : Arrays slots rows :=
  reconstruct rows repeats p slots record.1 record.2.1 record.2.2

def readRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) :
    Record rows repeats p slots :=
  let split := splitTape rows repeats p chosen q slots ω
  (split.1,
    (fun call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain (cutSlots p slots)) (split.2.1 call),
      belowEvaluate rows repeats chosen q (cutSlots p slots) split.2.2))

theorem reconstruct_original (rows repeats : Nat → Nat) :
    ∀ {n m k : Nat} (p : Path branch n (m + 1)) (chosen : Fin (branch m))
      (q : Path branch m k) (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (ω : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots),
      reconstructRecord rows repeats p slots (readRecord rows repeats p chosen q slots ω) =
        WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) slots ω := by
  intro n
  induction n with
  | zero =>
      intro m k p
      cases p
  | succ n ih =>
      intro m k p chosen q slots ω
      cases p with
      | refl => rfl
      | step i p =>
          exact congrArg₂ (WholeArraySampler.assemble slots rows)
            (reconstructBuckets_original rows repeats (.step i p) (.step chosen q) slots
              (ω (.inl ())))
            (congrArg (fun selected : Arrays (childSlots slots i) rows =>
              WholeArraySampler.childrenAt slots rows i selected (fun j => ω (.inr (.inr j))))
              (ih p chosen q (childSlots slots i) (ω (.inr (.inl ())))))

def callNumbering (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    OriginalCutCalls.Index rows repeats p ≃
      Fin (OriginalCutCalls.count rows repeats n (m + 1)) :=
  (Fintype.equivFin (OriginalCutCalls.Index rows repeats p)).trans
    (Equiv.cast (congrArg Fin (OriginalCutCalls.card_eq_count rows repeats p)))

def numberedValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (values : Values rows repeats p slots) :
    Fin (OriginalCutCalls.count rows repeats n (m + 1)) → H (cutSlots p slots) :=
  fun call => values ((callNumbering rows repeats p).symm call)

def reconstructNumbered (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (values : Fin (OriginalCutCalls.count rows repeats n (m + 1)) → H (cutSlots p slots))
    (below : BelowArrays rows p slots) : Arrays slots rows :=
  reconstruct rows repeats p slots exterior (fun call => values (callNumbering rows repeats p call)) below

theorem reconstructNumbered_numberedValues (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots) (values : Values rows repeats p slots)
    (below : BelowArrays rows p slots) :
    reconstructNumbered rows repeats p slots exterior (numberedValues rows repeats p slots values) below =
      reconstruct rows repeats p slots exterior values below := by
  apply congrArg (fun calls : Values rows repeats p slots =>
    reconstruct rows repeats p slots exterior calls below)
  funext call
  exact congrArg values ((callNumbering rows repeats p).symm_apply_apply call)

theorem reconstructNumbered_original (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) :
    let record := readRecord rows repeats p chosen q slots ω
    reconstructNumbered rows repeats p slots record.1
      (numberedValues rows repeats p slots record.2.1) record.2.2 =
        WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) slots ω := by
  dsimp only
  rw [reconstructNumbered_numberedValues]
  exact reconstruct_original rows repeats p chosen q slots ω

end
end PerfectCompleteness.OriginalWholeCut

end

end OAI
