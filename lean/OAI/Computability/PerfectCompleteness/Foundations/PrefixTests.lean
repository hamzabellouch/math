import Lean.Elab.Tactic.Omega
import OAI.Computability.PerfectCompleteness.Reduction.HierarchicalFixedAdviceFamilyLemmas

namespace OAI

section

namespace PerfectCompleteness.PrefixTests

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n cutoff : Nat}

theorem nodeAtLevel_eq (p : Path branch n cutoff) :
    ∀ (level : Fin n), cutoff ≤ level.val + 1 →
      ∀ suffix reference : Slots branch cutoff,
        GeometricPath.nodeAtLevel (p.slotEmbedding suffix) level =
          GeometricPath.nodeAtLevel (p.slotEmbedding reference) level := by
  induction p with
  | refl n =>
      intro level hlevel suffix reference
      cases n with
      | zero => exact Fin.elim0 level
      | succ n =>
          have hlast : level = Fin.last n := by
            apply Fin.ext
            simp only [Fin.val_last]
            omega
          subst level
          exact (GeometricPath.nodeAtLevel_last (branch := branch) (n := n) suffix).trans
            (GeometricPath.nodeAtLevel_last (branch := branch) (n := n) reference).symm
  | @step n cutoff i p ih =>
      intro level
      refine Fin.lastCases ?_ (fun lower => ?_) level
      · intro _ suffix reference
        exact (GeometricPath.nodeAtLevel_last (branch := branch) (n := n)
          ((Path.step i p).slotEmbedding suffix)).trans
            (GeometricPath.nodeAtLevel_last (branch := branch) (n := n)
              ((Path.step i p).slotEmbedding reference)).symm
      · intro hlevel suffix reference
        change cutoff ≤ lower.val + 1 at hlevel
        have hnode := congrArg (fun node : Nodes branch n =>
          (Sum.inr (i, node) : Nodes branch (n + 1)))
            (ih lower hlevel suffix reference)
        exact (GeometricPath.nodeAtLevel_castSucc (branch := branch) (n := n)
          ((Path.step i p).slotEmbedding suffix) lower).trans
            (hnode.trans (GeometricPath.nodeAtLevel_castSucc (branch := branch) (n := n)
              ((Path.step i p).slotEmbedding reference) lower).symm)

abbrev LevelDirection (rows : Nat → Nat) (level : Fin n) :=
  BucketSampler.Direction (rows (level.val + 1))

abbrev LevelNode (branch : Nat → Nat) {n : Nat} (level : Fin n) :=
  {node : Nodes branch n // Nodes.height node = level.val + 1}

def levelNode (leaf : Slots branch n) (level : Fin n) : LevelNode branch level :=
  ⟨GeometricPath.nodeAtLevel leaf level, GeometricPath.nodeAtLevel_height leaf level⟩

theorem levelNode_eq (p : Path branch n cutoff) (level : Fin n)
    (hlevel : cutoff ≤ level.val + 1) (suffix reference : Slots branch cutoff) :
    levelNode (p.slotEmbedding suffix) level = levelNode (p.slotEmbedding reference) level := by
  apply Subtype.ext
  exact nodeAtLevel_eq p level hlevel suffix reference

def nodeDirection (rows : Nat → Nat) (level : Fin n) (node : LevelNode branch level)
    (direction : LevelDirection rows level) :
    BucketSampler.Direction (rows (Nodes.height node.val)) :=
  (Equiv.cast (congrArg (fun height => BucketSampler.Direction (rows height)) node.property)).symm
    direction

def choiceAt (rows : Nat → Nat) (leaf : Slots branch n) (level : Fin n)
    (direction : LevelDirection rows level) : PreliminarySampler.Choice rows leaf :=
  ⟨level, nodeDirection rows level (levelNode leaf level) direction⟩

variable {v m t : Nat} {rows : Nat → Nat}

def observeAtLevelNode (clauses : Fin m → SourceClause.NormalizedClause v)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (q : PreliminarySampler.Questions branch n t m)
    (arrays : Arrays (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)) rows)
    (level : Fin n) (node : LevelNode branch level) (direction : LevelDirection rows level) : Bool :=
  let P := HierarchicalArrays.presentation clauses (PreliminarySampler.endpoints q) rows arrays
  let slots := SourceKeys.slot clauses ∘ P.endpoints
  let projection := BlockQuotient.projectBlock
    (V := fun node : Nodes branch n => Block rows node) (B := PUnit.{1})
    node.val (nodeDirection rows level node direction).val
  decide (CanonicalEdges.coarsen slots P.joint projection
      (KeyStrategy.label σ .left slots P.joint) =
    KeyStrategy.label σ .right slots (projection ∘ P.joint))

theorem observe_choiceAt_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (q : PreliminarySampler.Questions branch n t m)
    (arrays : Arrays (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)) rows)
    (leaf : Slots branch n) (level : Fin n) (direction : LevelDirection rows level) :
    PreliminaryStrategy.observe clauses σ (q, leaf) arrays (choiceAt rows leaf level direction) =
      observeAtLevelNode clauses σ q arrays level (levelNode leaf level) direction := rfl

theorem observe_above_cut_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (q : PreliminarySampler.Questions branch n t m)
    (arrays : Arrays (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)) rows)
    (p : Path branch n cutoff) (level : Fin n) (hlevel : cutoff ≤ level.val + 1)
    (suffix reference : Slots branch cutoff) (direction : LevelDirection rows level) :
    PreliminaryStrategy.observe clauses σ (q, p.slotEmbedding suffix) arrays
        (choiceAt rows (p.slotEmbedding suffix) level direction) =
      PreliminaryStrategy.observe clauses σ (q, p.slotEmbedding reference) arrays
        (choiceAt rows (p.slotEmbedding reference) level direction) := by
  simp only [observe_choiceAt_eq]
  exact congrArg (fun node : LevelNode branch level =>
    observeAtLevelNode clauses σ q arrays level node direction)
      (levelNode_eq p level hlevel suffix reference)

end
end PerfectCompleteness.PrefixTests

end

end OAI
