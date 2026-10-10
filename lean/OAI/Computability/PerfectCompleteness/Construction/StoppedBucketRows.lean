import OAI.Computability.PerfectCompleteness.Decoding.SelectedArrayProjection
import OAI.Computability.PerfectCompleteness.Sampling.WholeArrayBucketsLaw

namespace OAI

section

namespace PerfectCompleteness.StoppedBucketRows

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit SelectedArrayReplacement
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {N n m t : Nat}

theorem selectedRows_evaluate (rows repeats : Nat → Nat)
    (p : Path branch N (n + 1)) (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) :
    selectedRows rows p slots
        (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) slots tape) =
      BucketSampler.evaluate (rows (n + 1))
        (RecursiveSampler.evaluate F2 repeats (.step chosen q)
          (LeafDomain (WholeCutGrouping.cutSlots p slots)))
        (WholeArrayBucketsLaw.split rows repeats p chosen q slots tape).1 := by
  exact congrArg
    (fun arrays : Arrays (subtreeSlots p slots) rows => arrays (.inl ()))
    (restrictArrays_evaluate rows repeats p (.step chosen q) slots tape)

theorem pullback_bucket_evaluate {Ω : Type*} (width : Nat)
    {left right : Slots branch n → Fin t → MixedSupport.Slot}
    (projection : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (eval : Ω → H right) (tape : BucketSampler.Tape width Ω) :
    (fun row => HPullback projection (BucketSampler.evaluate width eval tape row)) =
      BucketSampler.evaluate width id (fun direction => HPullback projection (eval (tape direction))) := by
  funext row
  simp only [BucketSampler.evaluate, map_sum, map_smul, id_eq]

theorem selectedRows_pullback_evaluate (rows repeats : Nat → Nat)
    (p : Path branch N (n + 1)) (chosen : Fin (branch n)) (q : Path branch n m)
    (left right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right) :
    selectedRows rows p left
        (ChildBlockProjection.arraysPullback rows projection
          (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right tape)) =
      BucketSampler.evaluate (rows (n + 1)) id
        (fun direction => HPullback (CutGroupedProjection.cutProjection p projection)
          (RecursiveSampler.evaluate F2 repeats (.step chosen q)
            (LeafDomain (WholeCutGrouping.cutSlots p right))
            ((WholeArrayBucketsLaw.split rows repeats p chosen q right tape).1 direction))) := by
  rw [SelectedArrayProjection.selectedRows_pullback]
  simp only [selectedRows_evaluate rows repeats p chosen q right tape]
  exact pullback_bucket_evaluate (rows (n + 1))
    (CutGroupedProjection.cutProjection p projection)
    (RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain (WholeCutGrouping.cutSlots p right)))
    (WholeArrayBucketsLaw.split rows repeats p chosen q right tape).1

end
end PerfectCompleteness.StoppedBucketRows

end

end OAI
