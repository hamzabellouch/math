import OAI.Computability.PerfectCompleteness.Construction.NodeEmbedding
import OAI.Computability.PerfectCompleteness.Decoding.DecoderSourcePullback

namespace OAI

section

namespace PerfectCompleteness.ProjectedNodeEmbedding

noncomputable section

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open ChildBlockProjection (nodeProjection squarePullback)

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
  (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
  (upper : Nodes branch n)

def nativePullback :
    NodeEmbedding.NodeH projected upper →ₗ[F2] NodeEmbedding.NodeH slots upper :=
  HPullback (nodeProjection p upper)

@[simp] theorem nativePullback_apply
    (f : NodeEmbedding.NodeH projected upper) (x : Domain (nodeSlots slots upper)) :
    (nativePullback p upper f).val x =
      f.val (sourceProjection (nodeProjection p upper) x) := rfl

theorem nativePullback_injective : Function.Injective (nativePullback p upper) :=
  HPullback_injective (nodeProjection p upper)

def intoOriginal :
    NodeEmbedding.NodeH projected upper →ₗ[F2] NodeEmbedding.RowSpace slots upper :=
  (NodeEmbedding.embed slots upper).comp (nativePullback p upper)

theorem intoOriginal_injective : Function.Injective (intoOriginal p upper) :=
  (NodeEmbedding.embed_injective slots upper).comp (nativePullback_injective p upper)

@[simp] theorem intoOriginal_apply
    (f : NodeEmbedding.NodeH projected upper) (x : NodeEmbedding.NumberedDomain slots) :
    (intoOriginal p upper f).val x =
      f.val (sourceProjection (nodeProjection p upper)
        (NodeEmbedding.numberedRestriction slots upper x)) := rfl

theorem numberedRestriction_projection (x : NodeEmbedding.NumberedDomain slots) :
    sourceProjection (nodeProjection p upper) (NodeEmbedding.numberedRestriction slots upper x) =
      NodeEmbedding.numberedRestriction projected upper
        (MixedSupport.projectionMap (TreeCanonical.numberedProjection p) x) := by
  change restrictNode projected upper
    (sourceProjection p ((TreeCanonical.assignmentEquiv slots).symm x)) = _
  exact congrArg (restrictNode projected upper)
    (TreeCanonical.assignmentEquiv_symm_projection p x)

theorem intoOriginal_apply_projected
    (f : NodeEmbedding.NodeH projected upper) (x : NodeEmbedding.NumberedDomain slots) :
    (intoOriginal p upper f).val x =
      (NodeEmbedding.embed projected upper f).val
        (MixedSupport.projectionMap (TreeCanonical.numberedProjection p) x) := by
  exact congrArg f.val (numberedRestriction_projection p upper x)

theorem intoOriginal_val (f : NodeEmbedding.NodeH projected upper) :
    (intoOriginal p upper f).val =
      PointwiseSpaces.pullback F2
        (MixedSupport.projectionMap (TreeCanonical.numberedProjection p))
        (NodeEmbedding.embed projected upper f).val := by
  funext x
  exact intoOriginal_apply_projected p upper f x

theorem intoOriginal_at_assignment
    (f : NodeEmbedding.NodeH projected upper) (x : Domain slots) :
    (intoOriginal p upper f).val (TreeCanonical.assignmentEquiv slots x) =
      f.val (restrictNode projected upper (sourceProjection p x)) := by
  change f.val (sourceProjection (nodeProjection p upper)
    (restrictNode slots upper ((TreeCanonical.assignmentEquiv slots).symm
      (TreeCanonical.assignmentEquiv slots x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem dualMap_eq_upperTarget
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    (intoOriginal p upper).dualMap q = DecoderSourcePullback.upperTarget p upper q := by
  apply LinearMap.ext
  intro f
  rfl

theorem evaluation_dualMap (x : NodeEmbedding.NumberedDomain slots) :
    (intoOriginal p upper).dualMap
        (EvaluationMatrix.evaluation (NodeEmbedding.RowSpace slots upper) x) =
      EvaluationMatrix.evaluation (NodeEmbedding.NodeH projected upper)
        (NodeEmbedding.numberedRestriction projected upper
          (MixedSupport.projectionMap (TreeCanonical.numberedProjection p) x)) := by
  apply LinearMap.ext
  intro f
  exact congrArg f.val (numberedRestriction_projection p upper x)

theorem intoOriginal_mul (f g : NodeEmbedding.NodeH projected upper) :
    (intoOriginal p upper f).val * (intoOriginal p upper g).val =
      PointwiseSpaces.pullback F2
        (sourceProjection (nodeProjection p upper) ∘ NodeEmbedding.numberedRestriction slots upper)
        (f.val * g.val) := rfl

def intoOriginalSquare :
    PointwiseSpaces.squareSpace (NodeEmbedding.NodeH projected upper) →ₗ[F2]
      PointwiseSpaces.squareSpace (NodeEmbedding.RowSpace slots upper) where
  toFun f := ⟨PointwiseSpaces.pullback F2 (NodeEmbedding.numberedRestriction slots upper)
    (squarePullback (nodeProjection p upper) f).val, by
      rw [NodeEmbedding.squareSpace_eq]
      exact Submodule.mem_map_of_mem (squarePullback (nodeProjection p upper) f).property⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

@[simp] theorem intoOriginalSquare_apply
    (f : PointwiseSpaces.squareSpace (NodeEmbedding.NodeH projected upper))
    (x : NodeEmbedding.NumberedDomain slots) :
    (intoOriginalSquare p upper f).val x =
      f.val (sourceProjection (nodeProjection p upper)
        (NodeEmbedding.numberedRestriction slots upper x)) := rfl

theorem intoOriginalSquare_product (f g : NodeEmbedding.NodeH projected upper) :
    intoOriginalSquare p upper
        (OddListExtraction.productElement (NodeEmbedding.NodeH projected upper) f g) =
      OddListExtraction.productElement (NodeEmbedding.RowSpace slots upper)
        (intoOriginal p upper f) (intoOriginal p upper g) := by
  apply Subtype.ext
  rfl

end
end PerfectCompleteness.ProjectedNodeEmbedding

end

end OAI
