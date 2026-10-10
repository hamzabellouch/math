import OAI.Computability.PerfectCompleteness.Decoding.ChildBlockProjection
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalLeftDecoder
import OAI.Computability.PerfectCompleteness.Decoding.RightDecoderLemmas

namespace OAI


namespace PerfectCompleteness.DecoderSourcePullback

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces OwnInputReference
open ChildBlockProjection

noncomputable section

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}

def relativeCut :
    {n : Nat} → (upper : Nodes branch n) →
      (lower : Nodes branch (Nodes.height upper)) →
      Nodes.height lower < Nodes.height upper →
      Cut upper (RelativeDescendantProducts.relativeNode upper lower)
  | 0, upper, _, _ => nomatch upper
  | _ + 1, .inl _, lower, h =>
      { proper := h
        path := Nodes.path lower
        slots_agree := fun _ => rfl }
  | _ + 1, .inr (i, upper), lower, h =>
      let c := relativeCut upper lower h
      { proper := c.proper
        path := c.path
        slots_agree := fun s => congrArg (fun z => (i, z)) (c.slots_agree s) }

def selectedCut (upper : Nodes branch n) (level : Nat)
    (d : HierarchicalFrozenTables.LowerNodes upper level) :
    Cut upper (HierarchicalLeftDecoder.LowerNode upper level d) :=
  relativeCut upper d.val.val d.val.property

theorem upperBranch (upper : Nodes branch n) (hbranch : ∀ k < n, 0 < branch k) :
    ∀ k < Nodes.height upper, 0 < branch k :=
  fun k hk => hbranch k (Nat.lt_of_lt_of_le hk (Nodes.height_le upper))

variable (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
  (upper lower : Nodes branch n) (cut : Cut upper lower)

theorem restriction_projection (x : Domain (nodeSlots slots upper)) :
    RightDecoderDescendant.restriction projected upper lower cut
        (sourceProjection (nodeProjection p upper) x) =
      sourceProjection (nodeProjection p lower)
        (RightDecoderDescendant.restriction slots upper lower cut x) := by
  obtain ⟨y, rfl⟩ := restrictNode_surjective slots upper x
  rw [restrictNode_projection, RightDecoderDescendant.restriction_restrictNode,
    RightDecoderDescendant.restriction_restrictNode]
  exact (restrictNode_projection p lower y).symm

theorem squareEmbedding_pullback
    (hbranch : ∀ k < Nodes.height upper, 0 < branch k) :
    (HPullback (nodeProjection p upper)).comp
        (RightDecoderDescendant.squareEmbedding projected upper lower cut hbranch) =
      (RightDecoderDescendant.squareEmbedding slots upper lower cut hbranch).comp
        (squarePullback (nodeProjection p lower)) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change f.val (RightDecoderDescendant.restriction projected upper lower cut
      (sourceProjection (nodeProjection p upper) x)) =
    f.val (sourceProjection (nodeProjection p lower)
      (RightDecoderDescendant.restriction slots upper lower cut x))
  rw [restriction_projection p upper lower cut]

theorem squarePullback_product (f g : H projected) :
    squarePullback p (OddListExtraction.productElement (H projected) f g) =
      OddListExtraction.productElement (H slots) (HPullback p f) (HPullback p g) := by
  apply Subtype.ext
  rfl

def upperTarget (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    Module.Dual F2 (UpperSpace projected upper) :=
  (q.comp (NodeEmbedding.equiv slots upper).toLinearMap).comp
    (HPullback (nodeProjection p upper))

@[simp] theorem upperTarget_apply
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (f : UpperSpace projected upper) :
    upperTarget p upper q f =
      q (NodeEmbedding.embed slots upper (HPullback (nodeProjection p upper) f)) := rfl


variable (level : Nat) (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

theorem embed_squareEmbedding
    (cut : Cut upper (HierarchicalLeftDecoder.LowerNode upper level d)) :
    (NodeEmbedding.embed slots upper).comp
        (RightDecoderDescendant.squareEmbedding slots upper
          (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)) =
      HierarchicalLeftDecoder.squareEmbedding slots upper level hbranch d := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (RightDecoderDescendant.squareEmbedding slots upper
      (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch) f).val
        (restrictNode slots upper ((TreeCanonical.assignmentEquiv slots).symm x)) =
    f.val (restrictNode slots (HierarchicalLeftDecoder.LowerNode upper level d)
      ((TreeCanonical.assignmentEquiv slots).symm x))
  exact RightDecoderDescendant.squareEmbedding_restrictNode slots upper
    (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch) f
    ((TreeCanonical.assignmentEquiv slots).symm x)

theorem functional_upperTarget
    (cut : Cut upper (HierarchicalLeftDecoder.LowerNode upper level d))
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    RightDecoderDescendant.functional projected upper
        (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
        (upperTarget p upper q) =
      (HierarchicalLeftDecoder.output slots upper level hbranch d q).comp
        (squarePullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d))) := by
  apply LinearMap.ext
  intro f
  change q (NodeEmbedding.embed slots upper
      (HPullback (nodeProjection p upper)
        (RightDecoderDescendant.squareEmbedding projected upper
          (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch) f))) =
    q (HierarchicalLeftDecoder.squareEmbedding slots upper level hbranch d
      (squarePullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) f))
  calc
    _ = q (NodeEmbedding.embed slots upper
        (RightDecoderDescendant.squareEmbedding slots upper
          (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
          (squarePullback (nodeProjection p
            (HierarchicalLeftDecoder.LowerNode upper level d)) f))) :=
      congrArg (fun g => q (NodeEmbedding.embed slots upper g))
        (LinearMap.congr_fun (squareEmbedding_pullback p upper
          (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)) f)
    _ = _ := congrArg q (LinearMap.congr_fun
      (embed_squareEmbedding (slots := slots) upper level hbranch d cut)
      (squarePullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) f))

theorem form_upperTarget
    (cut : Cut upper (HierarchicalLeftDecoder.LowerNode upper level d))
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (f g : H (nodeSlots projected (HierarchicalLeftDecoder.LowerNode upper level d))) :
    RightDecoderDescendant.form projected upper
        (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
        (upperTarget p upper q) f g =
      OddListExtraction.multiplicationForm
        (H (nodeSlots slots (HierarchicalLeftDecoder.LowerNode upper level d)))
        (HierarchicalLeftDecoder.output slots upper level hbranch d q)
        (HPullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) f)
        (HPullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) g) := by
  change RightDecoderDescendant.functional projected upper
      (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
      (upperTarget p upper q)
      (OddListExtraction.productElement
        (H (nodeSlots projected (HierarchicalLeftDecoder.LowerNode upper level d))) f g) = _
  rw [functional_upperTarget p upper level hbranch d cut q]
  change (HierarchicalLeftDecoder.output slots upper level hbranch d q)
      (squarePullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d))
        (OddListExtraction.productElement
          (H (nodeSlots projected (HierarchicalLeftDecoder.LowerNode upper level d))) f g)) = _
  rw [squarePullback_product]
  rfl

theorem form_eq_of_target_error
    (cut : Cut upper (HierarchicalLeftDecoder.LowerNode upper level d))
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace projected upper)))
    (decoded : Module.Dual F2 (UpperSpace projected upper))
    (herror : decoded - upperTarget p upper q ∈ Q)
    (hvanish : ∀ z ∈ Q, z.comp
      (RightDecoderDescendant.squareEmbedding projected upper
        (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)) = 0)
    (f g : H (nodeSlots projected (HierarchicalLeftDecoder.LowerNode upper level d))) :
    RightDecoderDescendant.form projected upper
        (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
        decoded f g =
      OddListExtraction.multiplicationForm
        (H (nodeSlots slots (HierarchicalLeftDecoder.LowerNode upper level d)))
        (HierarchicalLeftDecoder.output slots upper level hbranch d q)
        (HPullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) f)
        (HPullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) g) := by
  rw [RightDecoderDescendant.form_eq_of_sub_mem projected upper
    (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
    Q decoded (upperTarget p upper q) herror hvanish]
  exact form_upperTarget p upper level hbranch d cut q f g


end
end PerfectCompleteness.DecoderSourcePullback

end OAI
