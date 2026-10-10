import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalPrediction
import OAI.Computability.PerfectCompleteness.Reduction.HierarchicalFixedAdviceFamilyLemmas

namespace OAI

section

namespace PerfectCompleteness.PreliminaryMatrixAcceptance

noncomputable section

open scoped Classical
open PreliminarySampler TreeSourceSpaces HierarchicalArrays

variable {v m n t : Nat} {branch rows : Nat → Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (b : Base branch n t m)

theorem observe_iff_matrix_accepts
    (arrays : Arrays (sourceSlots clauses (endpoints b.1)) rows)
    (choice : Choice rows b.2) :
    PreliminaryStrategy.observe clauses σ b arrays choice = true ↔
      CanonicalMatrixTable.Accepts
        (TreeCanonical.numberedSlots (sourceSlots clauses (endpoints b.1)))
        (NodeEmbedding.RowSpace (sourceSlots clauses (endpoints b.1))
          (GeometricPath.nodeAtLevel b.2 choice.1))
        (HierarchicalMatrixTable.other (sourceSlots clauses (endpoints b.1))
          (GeometricPath.nodeAtLevel b.2 choice.1)
          (HierarchicalMatrixTable.backgroundOf (sourceSlots clauses (endpoints b.1))
            (GeometricPath.nodeAtLevel b.2 choice.1) arrays))
        σ choice.2.val (NodeEmbedding.matrix arrays (GeometricPath.nodeAtLevel b.2 choice.1)) := by
  have h := (HierarchicalMatrixTable.accepts_iff_canonical
    (sourceSlots clauses (endpoints b.1)) (GeometricPath.nodeAtLevel b.2 choice.1) σ
    (HierarchicalMatrixTable.backgroundOf (sourceSlots clauses (endpoints b.1))
      (GeometricPath.nodeAtLevel b.2 choice.1) arrays)
    (NodeEmbedding.matrix arrays (GeometricPath.nodeAtLevel b.2 choice.1)) choice.2.val).symm
  rw [HierarchicalMatrixTable.displayed_original] at h
  unfold PreliminaryStrategy.observe
  dsimp only
  constructor
  · intro hobserve
    exact h.mp (@of_decide_eq_true _ _ hobserve)
  · intro haccepts
    exact @decide_eq_true _ _ (h.mpr haccepts)

theorem observe_eq_decide_matrix_accepts
    (arrays : Arrays (sourceSlots clauses (endpoints b.1)) rows)
    (choice : Choice rows b.2) :
    PreliminaryStrategy.observe clauses σ b arrays choice =
      decide (CanonicalMatrixTable.Accepts
        (TreeCanonical.numberedSlots (sourceSlots clauses (endpoints b.1)))
        (NodeEmbedding.RowSpace (sourceSlots clauses (endpoints b.1))
          (GeometricPath.nodeAtLevel b.2 choice.1))
        (HierarchicalMatrixTable.other (sourceSlots clauses (endpoints b.1))
          (GeometricPath.nodeAtLevel b.2 choice.1)
          (HierarchicalMatrixTable.backgroundOf (sourceSlots clauses (endpoints b.1))
            (GeometricPath.nodeAtLevel b.2 choice.1) arrays))
        σ choice.2.val (NodeEmbedding.matrix arrays (GeometricPath.nodeAtLevel b.2 choice.1))) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using observe_iff_matrix_accepts clauses σ b arrays choice

theorem observe_assembled_iff_lower_accepts (upper : Nodes branch n)
    (background : HierarchicalMatrixTable.Background (rows := rows)
      (sourceSlots clauses (endpoints b.1)) upper)
    (X : HierarchicalMatrixTable.Matrix (rows := rows) (sourceSlots clauses (endpoints b.1)) upper)
    (choice : Choice rows b.2) :
    PreliminaryStrategy.observe clauses σ b
        (HierarchicalMatrixTable.assemble (sourceSlots clauses (endpoints b.1)) upper background X)
        choice = true ↔
      HierarchicalPrediction.LowerAccepts (sourceSlots clauses (endpoints b.1)) upper
        background σ (GeometricPath.nodeAtLevel b.2 choice.1) choice.2.val X := by
  unfold PreliminaryStrategy.observe
  dsimp only
  constructor
  · intro hobserve
    have hcanonical := @of_decide_eq_true _ _ hobserve
    exact hcanonical
  · intro haccepts
    exact @decide_eq_true _ _ haccepts

theorem observe_iff_lower_accepts
    (arrays : Arrays (sourceSlots clauses (endpoints b.1)) rows)
    (choice : Choice rows b.2) (upper : Nodes branch n) :
    PreliminaryStrategy.observe clauses σ b arrays choice = true ↔
      HierarchicalPrediction.LowerAccepts (sourceSlots clauses (endpoints b.1)) upper
        (HierarchicalMatrixTable.backgroundOf (sourceSlots clauses (endpoints b.1)) upper arrays)
        σ (GeometricPath.nodeAtLevel b.2 choice.1) choice.2.val (NodeEmbedding.matrix arrays upper) := by
  have h := observe_assembled_iff_lower_accepts clauses σ b upper
    (HierarchicalMatrixTable.backgroundOf (sourceSlots clauses (endpoints b.1)) upper arrays)
    (NodeEmbedding.matrix arrays upper) choice
  rwa [HierarchicalMatrixTable.assemble_original] at h

end
end PerfectCompleteness.PreliminaryMatrixAcceptance

end

end OAI
