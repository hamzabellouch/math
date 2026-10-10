import OAI.Computability.PerfectCompleteness.Decoding.LowerCutNodeCoordinates
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutPairLemmas
import OAI.Computability.PerfectCompleteness.Machines.OwnInputReferenceLemmas

namespace OAI

section

namespace PerfectCompleteness.LowerCutOwnInput

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior
open scoped Classical TensorProduct

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : Slots branch n → Fin t → MixedSupport.Slot) (rows : Nat → Nat)
  (upper lower : Nodes branch n)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))

def ofArrays (a : Block rows lower)
    (known : HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper)
    (arrays : Arrays slots rows) : OwnInputReference.Input slots rows upper lower W a :=
  OwnInputReference.readInput slots rows upper lower W a id
    (known, OwnInputCanonicalQuery.exteriorOf slots rows upper lower arrays)

theorem ofArrays_update
    (a : BucketSampler.Direction (rows (Nodes.height lower)))
    (known : HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper)
    (arrays : Arrays slots rows) (fresh : H (nodeSlots slots lower)) :
    ofArrays slots rows upper lower W a.val known
        (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh)) =
      ofArrays slots rows upper lower W a.val known arrays := by
  have hother :
      (fun node : OwnInputReference.OtherNodes upper lower =>
        Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh) node.val) =
      (fun node : OwnInputReference.OtherNodes upper lower => arrays node.val) := by
    funext node
    exact Function.update_of_ne node.property.2 _ _
  change
    (OwnInputReference.Input.mk known
      (fun node : OwnInputReference.OtherNodes upper lower =>
        Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh) node.val)
      (LowerDirectionFiber.quotientQuery (H (nodeSlots slots lower)) a
        (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh) lower))) =
    (OwnInputReference.Input.mk known
      (fun node : OwnInputReference.OtherNodes upper lower => arrays node.val)
      (LowerDirectionFiber.quotientQuery (H (nodeSlots slots lower)) a (arrays lower)))
  rw [hother, Function.update_self, LowerDirectionFiber.quotientQuery_replace]

theorem query_update
    (a : BucketSampler.Direction (rows (Nodes.height lower)))
    (known : HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper)
    (arrays : Arrays slots rows) (fresh : H (nodeSlots slots lower))
    (hidden : W ⊗[F2] OwnInputReference.UpperSpace slots upper) :
    OwnInputReference.query slots rows upper lower W a.val
        (ofArrays slots rows upper lower W a.val known
          (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh))) hidden =
      OwnInputReference.query slots rows upper lower W a.val
        (ofArrays slots rows upper lower W a.val known arrays) hidden := by
  rw [ofArrays_update]

theorem response_update
    (a : BucketSampler.Direction (rows (Nodes.height lower)))
    (known : HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper)
    (arrays : Arrays slots rows) (fresh : H (nodeSlots slots lower))
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (hidden : W ⊗[F2] OwnInputReference.UpperSpace slots upper) :
    OwnInputReference.response slots rows upper lower W a.val labeling
        (ofArrays slots rows upper lower W a.val known
          (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh))) hidden =
      OwnInputReference.response slots rows upper lower W a.val labeling
        (ofArrays slots rows upper lower W a.val known arrays) hidden := by
  rw [ofArrays_update]

theorem quotientFullJoint_update
    (a : BucketSampler.Direction (rows (Nodes.height lower)))
    (arrays : Arrays slots rows) (fresh : H (nodeSlots slots lower)) :
    (BlockQuotient.projectBlock lower a.val ∘ fullJoint
      (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh))) =
    (BlockQuotient.projectBlock lower a.val ∘ fullJoint arrays) := by
  funext x
  apply Prod.ext
  · change LowerDirectionFiber.quotientQuery (H (nodeSlots slots lower)) a
        (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh) lower)
        (restrictNode slots lower x) =
      LowerDirectionFiber.quotientQuery (H (nodeSlots slots lower)) a (arrays lower)
        (restrictNode slots lower x)
    rw [Function.update_self, LowerDirectionFiber.quotientQuery_replace]
  · apply Prod.ext
    · funext node row
      change (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh)
          node.val row).val (restrictNode slots node.val x) =
        (arrays node.val row).val (restrictNode slots node.val x)
      rw [Function.update_of_ne node.property]
    · rfl

theorem canonicalQuery_update
    (a : BucketSampler.Direction (rows (Nodes.height lower)))
    (arrays : Arrays slots rows) (fresh : H (nodeSlots slots lower)) :
    OwnInputCanonicalQuery.canonicalQuery slots rows lower a.val
        (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh)) =
      OwnInputCanonicalQuery.canonicalQuery slots rows lower a.val arrays := by
  have h := congrArg (TreeCanonical.numberedFunction slots)
    (quotientFullJoint_update slots rows lower a arrays fresh)
  exact h

variable {m : Nat} (repeats : Nat → Nat) (p : Path branch n (m + 1))

theorem second_eq_update
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    LowerCutPair.second rows repeats p slots exterior a raw =
      Function.update (LowerCutPair.first rows repeats p slots exterior raw) (upperNode p)
        (LowerDirectionFiber.replace (LowerCutNodeCoordinates.directionEquiv rows p a)
          (LowerCutPair.first rows repeats p slots exterior raw (upperNode p))
          (LowerCutNodeCoordinates.scalarEquiv p slots (LowerCutPair.fresh rows repeats p slots raw))) :=
  LowerCutNodeCoordinates.replace_fiber_eq_update rows p slots _ a _

theorem ofArrays_second
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (known : HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper)
    (raw : LowerCutPair.Raw rows repeats p slots) :
    ofArrays slots rows upper (upperNode p) W
        (LowerCutNodeCoordinates.directionEquiv rows p a).val known
        (LowerCutPair.second rows repeats p slots exterior a raw) =
      ofArrays slots rows upper (upperNode p) W
        (LowerCutNodeCoordinates.directionEquiv rows p a).val known
        (LowerCutPair.first rows repeats p slots exterior raw) := by
  rw [second_eq_update]
  exact ofArrays_update slots rows upper (upperNode p) W _ _ _ _

theorem query_second
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (known : HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper)
    (raw : LowerCutPair.Raw rows repeats p slots)
    (hidden : W ⊗[F2] OwnInputReference.UpperSpace slots upper) :
    OwnInputReference.query slots rows upper (upperNode p) W
        (LowerCutNodeCoordinates.directionEquiv rows p a).val
        (ofArrays slots rows upper (upperNode p) W
          (LowerCutNodeCoordinates.directionEquiv rows p a).val known
          (LowerCutPair.second rows repeats p slots exterior a raw)) hidden =
      OwnInputReference.query slots rows upper (upperNode p) W
        (LowerCutNodeCoordinates.directionEquiv rows p a).val
        (ofArrays slots rows upper (upperNode p) W
          (LowerCutNodeCoordinates.directionEquiv rows p a).val known
          (LowerCutPair.first rows repeats p slots exterior raw)) hidden := by
  rw [ofArrays_second]

theorem canonicalQuery_second
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    OwnInputCanonicalQuery.canonicalQuery slots rows (upperNode p)
        (LowerCutNodeCoordinates.directionEquiv rows p a).val
        (LowerCutPair.second rows repeats p slots exterior a raw) =
      OwnInputCanonicalQuery.canonicalQuery slots rows (upperNode p)
        (LowerCutNodeCoordinates.directionEquiv rows p a).val
        (LowerCutPair.first rows repeats p slots exterior raw) := by
  rw [second_eq_update]
  exact canonicalQuery_update slots rows (upperNode p) _ _ _

end
end PerfectCompleteness.LowerCutOwnInput

end

end OAI
