import Mathlib.LinearAlgebra.Dimension.Finrank
import OAI.Computability.PerfectCompleteness.Algebra.EvaluationMatrix
import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalArrays

namespace OAI


namespace PerfectCompleteness.NodeEmbedding

open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

abbrev NumberedDomain (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :=
  MixedSupport.Assignment (TreeCanonical.numberedSlots slots)

abbrev NodeH (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) := H (nodeSlots slots node)

variable (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (node : Nodes branch n)

def numberedRestriction : NumberedDomain slots → Domain (nodeSlots slots node) :=
  restrictNode slots node ∘ (TreeCanonical.assignmentEquiv slots).symm

theorem numberedRestriction_surjective : Function.Surjective (numberedRestriction slots node) :=
  (restrictNode_surjective slots node).comp (TreeCanonical.assignmentEquiv slots).symm.surjective

theorem pullback_injective :
    Function.Injective (PointwiseSpaces.pullback F2 (numberedRestriction slots node)) :=
  PointwiseSpaces.pullback_injective _ (numberedRestriction_surjective slots node)

def RowSpace : Submodule F2 (NumberedDomain slots → F2) :=
  (NodeH slots node).map (PointwiseSpaces.pullback F2 (numberedRestriction slots node))

def equiv : NodeH slots node ≃ₗ[F2] RowSpace slots node :=
  Submodule.equivMapOfInjective
    (PointwiseSpaces.pullback F2 (numberedRestriction slots node))
    (pullback_injective slots node) (NodeH slots node)

def embed : NodeH slots node →ₗ[F2] RowSpace slots node :=
  (equiv slots node).toLinearMap

@[simp] theorem equiv_apply (f : NodeH slots node) (x : NumberedDomain slots) :
    (equiv slots node f).val x = f.val (numberedRestriction slots node x) := rfl

@[simp] theorem embed_apply (f : NodeH slots node) (x : NumberedDomain slots) :
    (embed slots node f).val x = f.val (numberedRestriction slots node x) := rfl

theorem embed_injective : Function.Injective (embed slots node) :=
  (equiv slots node).injective

theorem embed_surjective : Function.Surjective (embed slots node) :=
  (equiv slots node).surjective

theorem finrank_eq :
    Module.finrank F2 (RowSpace slots node) = Module.finrank F2 (NodeH slots node) :=
  (equiv slots node).finrank_eq.symm

theorem card_eq : Nat.card (RowSpace slots node) = Nat.card (NodeH slots node) :=
  (Nat.card_congr (equiv slots node).toEquiv).symm

theorem uniform_embed [Fintype (NodeH slots node)] [Fintype (RowSpace slots node)] :
    (FiniteDistribution.uniform (NodeH slots node)).pushforward (embed slots node) =
      FiniteDistribution.uniform (RowSpace slots node) :=
  UniformLinearImage.uniform_pushforward_linearMap (embed slots node)
    (embed_surjective slots node)

def rowsEquiv (ℓ : Nat) :
    (Fin ℓ → NodeH slots node) ≃ₗ[F2] (Fin ℓ → RowSpace slots node) :=
  LinearEquiv.piCongrRight (fun _ : Fin ℓ => equiv slots node)

@[simp] theorem rowsEquiv_apply (ℓ : Nat) (f : Fin ℓ → NodeH slots node) (i : Fin ℓ) :
    rowsEquiv slots node ℓ f i = embed slots node (f i) := rfl

theorem uniform_rowsEquiv (ℓ : Nat)
    [Fintype (NodeH slots node)] [Fintype (RowSpace slots node)] :
    (FiniteDistribution.uniform (Fin ℓ → NodeH slots node)).pushforward
        (rowsEquiv slots node ℓ) =
      FiniteDistribution.uniform (Fin ℓ → RowSpace slots node) :=
  UniformLinearImage.uniform_pushforward_linearMap
    (rowsEquiv slots node ℓ).toLinearMap (rowsEquiv slots node ℓ).surjective

theorem squareSpace_eq :
    PointwiseSpaces.squareSpace (RowSpace slots node) =
      (PointwiseSpaces.squareSpace (NodeH slots node)).map
        (PointwiseSpaces.pullback F2 (numberedRestriction slots node)) :=
  (PointwiseSpaces.squareSpace_map_pullback
    (numberedRestriction slots node) (NodeH slots node)).symm

theorem embed_mul (f g : NodeH slots node) :
    (embed slots node f).val * (embed slots node g).val =
      PointwiseSpaces.pullback F2 (numberedRestriction slots node) (f.val * g.val) := rfl

def RootRowSpace : Submodule F2 (NumberedDomain slots → F2) :=
  (H slots).map (PointwiseSpaces.pullback F2 (TreeCanonical.assignmentEquiv slots).symm)

theorem rowSpace_le_root (hbranch : ∀ k < n, 0 < branch k) :
    RowSpace slots node ≤ RootRowSpace slots := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  have hroot : PointwiseSpaces.pullback F2 (restrictNode slots node) g ∈ H slots :=
    DescendantSpaces.space_descendant_le (Nodes.path node) (LeafDomain slots) hbranch
      (Submodule.mem_map_of_mem hg)
  exact Submodule.mem_map.mpr
    ⟨PointwiseSpaces.pullback F2 (restrictNode slots node) g, hroot, rfl⟩

theorem squareSpace_le_root (hbranch : ∀ k < n, 0 < branch k)
    (hproper : Nodes.height node < n) :
    PointwiseSpaces.squareSpace (RowSpace slots node) ≤ RootRowSpace slots := by
  rw [squareSpace_eq]
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  have hroot : PointwiseSpaces.pullback F2 (restrictNode slots node) g ∈ H slots :=
    DescendantSpaces.descendant_square_le_space (Nodes.path node) (LeafDomain slots)
      hbranch hproper (Submodule.mem_map_of_mem hg)
  exact Submodule.mem_map.mpr
    ⟨PointwiseSpaces.pullback F2 (restrictNode slots node) g, hroot, rfl⟩


variable {slots} {rows : Nat → Nat}

def embeddedRows (arrays : Arrays slots rows) (node : Nodes branch n) :
    Fin (rows (Nodes.height node)) → RowSpace slots node :=
  fun i => embed slots node (arrays node i)

@[simp] theorem embeddedRows_apply (arrays : Arrays slots rows) (node : Nodes branch n)
    (i : Fin (rows (Nodes.height node))) (x : NumberedDomain slots) :
    (embeddedRows arrays node i).val x =
      (TreeCanonical.numberedFunction slots (fullJoint arrays) x).1 node i := rfl

def matrix (arrays : Arrays slots rows) (node : Nodes branch n) :
    Module.Dual F2 (RowSpace slots node) →ₗ[F2] Block rows node :=
  EvaluationMatrix.ofRows (RowSpace slots node) (embeddedRows arrays node)

@[simp] theorem matrix_evaluate (arrays : Arrays slots rows) (node : Nodes branch n)
    (x : NumberedDomain slots) :
    EvaluationMatrix.evaluate (RowSpace slots node) (matrix arrays node) x =
      (TreeCanonical.numberedFunction slots (fullJoint arrays) x).1 node := rfl

theorem evaluation_comp_embed (x : NumberedDomain slots) :
    (EvaluationMatrix.evaluation (RowSpace slots node) x).comp (embed slots node) =
      EvaluationMatrix.evaluation (NodeH slots node) (numberedRestriction slots node x) := by
  ext f
  rfl

end
end PerfectCompleteness.NodeEmbedding

end OAI
