import OAI.Computability.PerfectCompleteness.Algebra.HierarchicalMatrixTable
import OAI.Computability.PerfectCompleteness.Foundations.QuarterBalanceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.BucketUniformLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeArraySampler

namespace OAI

section

namespace PerfectCompleteness.HierarchicalArrayLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

abbrev NativeRows (node : Nodes branch n) :=
  Fin (rows (Nodes.height node)) → NodeEmbedding.NodeH slots node

def law (μ : (node : Nodes branch n) → FiniteDistribution (NativeRows slots rows node)) :
    FiniteDistribution (Arrays slots rows) :=
  FiniteProduct.law μ

def otherLaw (μ : (node : Nodes branch n) → FiniteDistribution (NativeRows slots rows node))
    (node : Nodes branch n) :
    FiniteDistribution (HierarchicalMatrixTable.Background (rows := rows) slots node) :=
  FiniteProductSplit.otherLaw μ node

def nativeToMatrix (node : Nodes branch n) (v : NativeRows slots rows node) :
    HierarchicalMatrixTable.Matrix (rows := rows) slots node :=
  EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots node)
    (NodeEmbedding.rowsEquiv slots node (rows (Nodes.height node)) v)

@[simp] theorem nativeToMatrix_selected (arrays : Arrays slots rows) (node : Nodes branch n) :
    nativeToMatrix slots rows node (arrays node) = NodeEmbedding.matrix arrays node := rfl

private theorem pushforward_id {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    μ.pushforward (fun a => a) = μ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro a
  simp [FiniteDistribution.pushforward]

theorem matrix_background_law
    (μ : (node : Nodes branch n) → FiniteDistribution (NativeRows slots rows node))
    (node : Nodes branch n)
    [Fintype (HierarchicalMatrixTable.Matrix (rows := rows) slots node)] :
    (law slots rows μ).pushforward (fun arrays =>
        (NodeEmbedding.matrix arrays node, HierarchicalMatrixTable.backgroundOf slots node arrays)) =
      ((μ node).pushforward (nativeToMatrix slots rows node)).product
        (otherLaw slots rows μ node) := by
  have h := congrArg
    (fun ν : FiniteDistribution (NativeRows slots rows node ×
        HierarchicalMatrixTable.Background (rows := rows) slots node) =>
      ν.pushforward (fun p => (nativeToMatrix slots rows node p.1, p.2)))
    (FiniteProductSplit.split_law μ node)
  rw [FiniteDistribution.pushforward_comp] at h
  have hp := FiniteDistribution.product_pushforward
    (μ node) (FiniteProductSplit.otherLaw μ node) (nativeToMatrix slots rows node)
    (id : HierarchicalMatrixTable.Background (rows := rows) slots node →
      HierarchicalMatrixTable.Background (rows := rows) slots node)
  have hi : (FiniteProductSplit.otherLaw μ node).pushforward
      (id : HierarchicalMatrixTable.Background (rows := rows) slots node →
        HierarchicalMatrixTable.Background (rows := rows) slots node) =
      FiniteProductSplit.otherLaw μ node := pushforward_id (FiniteProductSplit.otherLaw μ node)
  rw [hi] at hp
  exact h.trans (by simpa only [id_eq, otherLaw] using hp)

theorem uniform_nativeToMatrix (node : Nodes branch n)
    [Fintype (HierarchicalMatrixTable.Matrix (rows := rows) slots node)] :
    (FiniteDistribution.uniform (NativeRows slots rows node)).pushforward
        (nativeToMatrix slots rows node) =
      FiniteDistribution.uniform (HierarchicalMatrixTable.Matrix (rows := rows) slots node) := by
  let : Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _
  calc
    _ = ((FiniteDistribution.uniform (NativeRows slots rows node)).pushforward
        (NodeEmbedding.rowsEquiv slots node (rows (Nodes.height node)))).pushforward
          (EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots node)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (FiniteDistribution.uniform
        (Fin (rows (Nodes.height node)) → NodeEmbedding.RowSpace slots node)).pushforward
          (EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots node)) := by
      rw [NodeEmbedding.uniform_rowsEquiv]
    _ = _ := UniformLinearImage.uniform_pushforward_linearMap
      (BucketUniform.ofRowsLinear (NodeEmbedding.RowSpace slots node) (rows (Nodes.height node)))
      (BucketUniform.ofRowsLinear_surjective
        (NodeEmbedding.RowSpace slots node) (rows (Nodes.height node)))

theorem uniform_matrix_background_law
    (μ : (node : Nodes branch n) → FiniteDistribution (NativeRows slots rows node))
    (node : Nodes branch n)
    [Fintype (HierarchicalMatrixTable.Matrix (rows := rows) slots node)]
    (hselected : μ node = FiniteDistribution.uniform (NativeRows slots rows node)) :
    (law slots rows μ).pushforward (fun arrays =>
        (NodeEmbedding.matrix arrays node, HierarchicalMatrixTable.backgroundOf slots node arrays)) =
      (FiniteDistribution.uniform
        (HierarchicalMatrixTable.Matrix (rows := rows) slots node)).product
          (otherLaw slots rows μ node) := by
  rw [matrix_background_law, hselected, uniform_nativeToMatrix]

theorem matrix_coarse_background_law
    (μ : (node : Nodes branch n) → FiniteDistribution (NativeRows slots rows node))
    (node : Nodes branch n)
    [Fintype (HierarchicalMatrixTable.Matrix (rows := rows) slots node)]
    {B : Type*} [Fintype B]
    (record : HierarchicalMatrixTable.Background (rows := rows) slots node → B) :
    (law slots rows μ).pushforward (fun arrays =>
        (NodeEmbedding.matrix arrays node, record (HierarchicalMatrixTable.backgroundOf slots node arrays))) =
      ((μ node).pushforward (nativeToMatrix slots rows node)).product
        ((otherLaw slots rows μ node).pushforward record) := by
  have h := congrArg
    (fun ν : FiniteDistribution
        (HierarchicalMatrixTable.Matrix (rows := rows) slots node ×
          HierarchicalMatrixTable.Background (rows := rows) slots node) =>
      ν.pushforward (fun p => (p.1, record p.2)))
    (matrix_background_law slots rows μ node)
  rw [FiniteDistribution.pushforward_comp] at h
  have hp := FiniteDistribution.product_pushforward
    ((μ node).pushforward (nativeToMatrix slots rows node)) (otherLaw slots rows μ node)
    (id : HierarchicalMatrixTable.Matrix (rows := rows) slots node →
      HierarchicalMatrixTable.Matrix (rows := rows) slots node) record
  have hi : ((μ node).pushforward (nativeToMatrix slots rows node)).pushforward
      (id : HierarchicalMatrixTable.Matrix (rows := rows) slots node →
        HierarchicalMatrixTable.Matrix (rows := rows) slots node) =
      (μ node).pushforward (nativeToMatrix slots rows node) :=
    pushforward_id ((μ node).pushforward (nativeToMatrix slots rows node))
  rw [hi] at hp
  exact h.trans (by simpa only [id_eq] using hp)

theorem uniform_matrix_coarse_background_law
    (μ : (node : Nodes branch n) → FiniteDistribution (NativeRows slots rows node))
    (node : Nodes branch n)
    [Fintype (HierarchicalMatrixTable.Matrix (rows := rows) slots node)]
    (hselected : μ node = FiniteDistribution.uniform (NativeRows slots rows node))
    {B : Type*} [Fintype B]
    (record : HierarchicalMatrixTable.Background (rows := rows) slots node → B) :
    (law slots rows μ).pushforward (fun arrays =>
        (NodeEmbedding.matrix arrays node, record (HierarchicalMatrixTable.backgroundOf slots node arrays))) =
      (FiniteDistribution.uniform
        (HierarchicalMatrixTable.Matrix (rows := rows) slots node)).product
          ((otherLaw slots rows μ node).pushforward record) := by
  rw [matrix_coarse_background_law, hselected, uniform_nativeToMatrix]

end
end PerfectCompleteness.HierarchicalArrayLaw

end

end OAI
