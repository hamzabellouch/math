import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas

namespace OAI

section

namespace PerfectCompleteness.ScalarTapeCardinality

open TreeSourceSpaces TreeCardinality RecursiveSampler DescendantSpaces
open scoped BigOperators

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def drawHeight (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → DrawIndex repeats p → Nat
  | n, _, .refl _, _ => n
  | n + 1, _, .step _ p, j =>
      match j with
      | Sum.inl _ => n
      | Sum.inr j => drawHeight repeats p j.2

def tapeBound (repeats : Nat → Nat) (p : Path branch n m) (t : Nat) : Nat :=
  ∏ j : DrawIndex repeats p, functionBound branch (drawHeight repeats p j) t

theorem drawSpace_card_le (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
      (j : DrawIndex repeats p),
      Nat.card (DrawSpace F2 repeats p (LeafDomain slots) j) ≤
        functionBound branch (drawHeight repeats p j) t := by
  induction p with
  | refl n =>
      intro slots j
      exact H_card_le slots
  | @step n m i p ih =>
      intro slots j
      cases j with
      | inl j => exact square_card_le (childSlots slots j.val)
      | inr j => exact ih (childSlots slots i) j.2

theorem tape_card_le (repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (Tape F2 repeats p (LeafDomain slots)) ≤ tapeBound repeats p t := by
  change Nat.card (∀ j : DrawIndex repeats p,
    DrawSpace F2 repeats p (LeafDomain slots) j) ≤ _
  rw [Nat.card_pi]
  exact Finset.prod_le_prod (fun j _ => drawSpace_card_le repeats p slots j)

def bucketBound (rows repeats : Nat → Nat) (p : Path branch n m) (t : Nat) : Nat :=
  tapeBound repeats p t ^ Nat.card (BucketSampler.Direction (rows n))

theorem bucket_card_le (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (BucketSampler.RecursiveTape (rows n) repeats p (LeafDomain slots)) ≤
      bucketBound rows repeats p t := by
  change Nat.card (BucketSampler.Direction (rows n) →
    Tape F2 repeats p (LeafDomain slots)) ≤ _
  rw [Nat.card_fun]
  exact pow_le_pow_left₀ (Nat.zero_le _) (tape_card_le repeats p slots) _

end
end PerfectCompleteness.ScalarTapeCardinality

end

end OAI
