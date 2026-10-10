import OAI.Computability.PerfectCompleteness.Algebra.PreliminaryMatrixAcceptance
import OAI.Computability.PerfectCompleteness.Foundations.PrefixTests
import OAI.Computability.PerfectCompleteness.Machines.StoppedOwnInputGeometry

namespace OAI

section

namespace PerfectCompleteness.PrefixMatrixAcceptance

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {v m n t : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (questions : PreliminarySampler.Questions branch n t m)

local notation "slots" => sourceSlots clauses (PreliminarySampler.endpoints questions)

theorem observe_iff_matrix
    (arrays : Arrays slots rows) (level : Fin n)
    (node : PrefixTests.LevelNode branch level)
    (a : PrefixTests.LevelDirection rows level) :
    PrefixTests.observeAtLevelNode clauses σ questions arrays level node a = true ↔
      CanonicalMatrixTable.Accepts (TreeCanonical.numberedSlots slots)
        (NodeEmbedding.RowSpace slots node.val)
        (HierarchicalMatrixTable.other slots node.val
          (HierarchicalMatrixTable.backgroundOf slots node.val arrays))
        σ (PrefixTests.nodeDirection rows level node a).val
        (NodeEmbedding.matrix arrays node.val) := by
  have h := (HierarchicalMatrixTable.accepts_iff_canonical slots node.val σ
    (HierarchicalMatrixTable.backgroundOf slots node.val arrays)
    (NodeEmbedding.matrix arrays node.val)
    (PrefixTests.nodeDirection rows level node a).val).symm
  rw [HierarchicalMatrixTable.displayed_original] at h
  unfold PrefixTests.observeAtLevelNode
  dsimp only
  constructor
  · intro hevent
    exact h.mp (@of_decide_eq_true _ _ hevent)
  · intro haccept
    exact @decide_eq_true _ _ (h.mpr haccept)

theorem observe_iff_lower
    (arrays : Arrays slots rows) (level : Fin n)
    (node : PrefixTests.LevelNode branch level)
    (a : PrefixTests.LevelDirection rows level) (upper : Nodes branch n) :
    PrefixTests.observeAtLevelNode clauses σ questions arrays level node a = true ↔
      HierarchicalPrediction.LowerAccepts slots upper
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) σ node.val
        (PrefixTests.nodeDirection rows level node a).val
        (NodeEmbedding.matrix arrays upper) := by
  unfold HierarchicalPrediction.LowerAccepts
  rw [HierarchicalMatrixTable.displayed_original]
  unfold PrefixTests.observeAtLevelNode
  dsimp only
  constructor
  · intro hevent
    exact @of_decide_eq_true _ _ hevent
  · intro haccept
    exact @decide_eq_true _ _ haccept

theorem observe_eq_lower
    (arrays : Arrays slots rows) (level : Fin n)
    (node : PrefixTests.LevelNode branch level)
    (a : PrefixTests.LevelDirection rows level) (upper : Nodes branch n) :
    PrefixTests.observeAtLevelNode clauses σ questions arrays level node a =
      decide (HierarchicalPrediction.LowerAccepts slots upper
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) σ node.val
        (PrefixTests.nodeDirection rows level node a).val
        (NodeEmbedding.matrix arrays upper)) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using
    observe_iff_lower clauses σ questions arrays level node a upper

theorem observe_endpoint {k : Nat} (p : Path branch n (k + 1))
    (suffix : Slots branch (k + 1)) (arrays : Arrays slots rows)
    (a : PrefixTests.LevelDirection rows
      (⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ : Fin n)) :
    PreliminaryStrategy.observe clauses σ (questions, p.slotEmbedding suffix) arrays
      (PrefixTests.choiceAt rows (p.slotEmbedding suffix)
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ a) =
      PrefixTests.observeAtLevelNode clauses σ questions arrays
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩
        ⟨WholeArrayInteriorExterior.upperNode p,
          WholeArrayInteriorExterior.upperNode_height p⟩ a := by
  rw [PrefixTests.observe_choiceAt_eq]
  apply congrArg (fun node => PrefixTests.observeAtLevelNode clauses σ questions arrays
    ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ node a)
  apply Subtype.ext
  exact StoppedOwnInputGeometry.nodeAtLevel_endpoint p suffix

end
end PerfectCompleteness.PrefixMatrixAcceptance

end

end OAI
