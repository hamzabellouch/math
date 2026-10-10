import OAI.Computability.PerfectCompleteness.Construction.SourcePhysicalTaggedChildren
import OAI.Computability.PerfectCompleteness.Decoding.CutProjectionAssembly
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutScalarProjectionLemmas
import OAI.Computability.PerfectCompleteness.Decoding.LowerProjectedOriginalSuccessLemmas
import OAI.Computability.PerfectCompleteness.Foundations.SourceProjectedTag

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPhysicalHigh

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)
  (q : SourceQuestionLowerForms.Questions
    (branch := branch) (height := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple
    (branch := branch) (n := height) (t := t))
  (flags : SourceProjectedTag.Flags (branch := branch) (n := height))

abbrev originalSlots := SourceQuestionLowerForms.slots path outside clauses q

def projectedSlots : Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill path outside
    (SourceProjectedTag.mixedInside clauses designated q choices flags)

def projection : ∀ leaf j, MixedSupport.Projection
    (originalSlots path outside clauses q leaf j)
    (projectedSlots path outside clauses designated q choices flags leaf j) :=
  CutProjectionAssembly.fillProjection path outside
    (SourceChildMarkedLaw.questionSlots clauses q)
    (SourceProjectedTag.mixedInside clauses designated q choices flags)
    (SourceProjectedTag.projection clauses designated q choices flags)

def exteriorAt
    (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder) :
    WholeCutGrouping.Exterior rows repeats path
      (projectedSlots path outside clauses designated q choices flags) :=
  CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
    (SourceProjectedTag.mixedInside clauses designated q choices flags) exterior

section Collision

variable (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)
  (direction : BucketSampler.Direction (rows (height + 1)))
  (cutoff : Nat)
  (table : SourceQuestionLowerForms.UpperTable (rows := rows)
    path outside clauses upper level (adviceRows := adviceRows) q)

def collision : ℝ :=
  LowerProjectedFiberAverage.rawCollision path
    (originalSlots path outside clauses q)
    (projectedSlots path outside clauses designated q choices flags)
    (projection path outside clauses designated q choices flags)
    upper level hbranch d direction
    (exteriorAt path outside placeholder clauses designated q choices flags exterior)
    A cutoff table

end Collision

section Success

variable (upper : Nodes branch n)
  (pDown : Path branch (Nodes.height upper) (height + 1))
  (hproper : height + 1 < Nodes.height upper)
  (level : Nat) (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode ((Nodes.path upper).append pDown) =
    HierarchicalLeftDecoder.LowerNode upper level d)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows)
      (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper level bg → Prop)
  (ρ threshold : ℝ)
  (exterior : CleanPhysicalReplay.Exterior rows repeats
    ((Nodes.path upper).append pDown) outside placeholder)
  (direction : BucketSampler.Direction (rows (height + 1)))
  (cutoff : Nat)

local instance rowSpaceFintype :
    Fintype (NodeEmbedding.RowSpace
      (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  Fintype.ofFinite _

local instance upperAnswerFintype :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace
    (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper)

def success : ℝ :=
  LowerPhysicalFiberSuccess.physicalSuccess
    (originalSlots ((Nodes.path upper).append pDown) outside clauses q)
    (projectedSlots ((Nodes.path upper).append pDown) outside clauses designated q choices flags)
    (projection ((Nodes.path upper).append pDown) outside clauses designated q choices flags)
    upper pDown hproper level hbranch d hnode direction
    (exteriorAt ((Nodes.path upper).append pDown) outside placeholder clauses designated
      q choices flags exterior) A cut σ useful ρ threshold cutoff

theorem success_square_le :
    success outside placeholder clauses designated q choices flags upper pDown hproper level
        hbranch d hnode A cut σ useful ρ threshold exterior direction cutoff ^ 2 ≤
      (HierarchicalAllDecoderTables.upperTableLaw
        (originalSlots ((Nodes.path upper).append pDown) outside clauses q)
        upper level σ useful adviceRows ρ).expectation
          (collision ((Nodes.path upper).append pDown) outside placeholder clauses designated
            q choices flags upper level d hbranch A exterior direction cutoff) :=
  LowerPhysicalFiberSuccess.physicalSuccess_square_le
    (originalSlots ((Nodes.path upper).append pDown) outside clauses q)
    (projectedSlots ((Nodes.path upper).append pDown) outside clauses designated q choices flags)
    (projection ((Nodes.path upper).append pDown) outside clauses designated q choices flags)
    upper pDown hproper level hbranch d hnode direction
    (exteriorAt ((Nodes.path upper).append pDown) outside placeholder clauses designated
      q choices flags exterior) A cut σ useful ρ threshold cutoff

end Success
end
end PerfectCompleteness.SourceQuestionPhysicalHigh

end

end OAI
