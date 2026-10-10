import OAI.Computability.PerfectCompleteness.Algebra.PrefixMatrixAcceptance
import OAI.Computability.PerfectCompleteness.Construction.StoppedProjectedBucketIndex
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAdviceExperimentLemmas
import OAI.Computability.PerfectCompleteness.Foundations.StoppedPathHead
import OAI.Computability.PerfectCompleteness.Sampling.StoppedUsefulPairLaw

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedUsefulEvent

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype

private theorem observe_assemble
    {branch rows : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (lowerLevel : Nat) (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (matrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) :
    HierarchicalUsefulness.observe slots upper lowerLevel
      (HierarchicalMatrixTable.assemble slots upper background matrix) =
      ⟨background, MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background) matrix⟩ := by
  have hbackground : HierarchicalMatrixTable.backgroundOf slots upper
      (HierarchicalMatrixTable.assemble slots upper background matrix) = background := by
    funext node row
    exact congrFun (HierarchicalMatrixTable.assemble_other slots upper background matrix node) row
  exact congrArg₂ (fun (b : HierarchicalMatrixTable.Background (rows := rows) slots upper)
      (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) =>
    (⟨b, MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel b) X⟩ :
      HierarchicalUsefulness.Coarse (rows := rows) slots upper lowerLevel))
    hbackground (HierarchicalMatrixTable.matrix_assemble slots upper background matrix)

private theorem upper_observe_assemble
    {branch rows : Nat → Nat} {n t v m : Nat}
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (questions : PreliminarySampler.Questions branch n t m)
    (level : Fin n) (node : PrefixTests.LevelNode branch level)
    (direction : PrefixTests.LevelDirection rows level)
    (background : HierarchicalMatrixTable.Background (rows := rows)
      (sourceSlots clauses (PreliminarySampler.endpoints questions)) node.val)
    (matrix : HierarchicalMatrixTable.Matrix (rows := rows)
      (sourceSlots clauses (PreliminarySampler.endpoints questions)) node.val) :
    PrefixTests.observeAtLevelNode clauses σ questions
        (HierarchicalMatrixTable.assemble
          (sourceSlots clauses (PreliminarySampler.endpoints questions)) node.val background matrix)
        level node direction =
      decide (CanonicalMatrixTable.Accepts
        (TreeCanonical.numberedSlots (sourceSlots clauses (PreliminarySampler.endpoints questions)))
        (NodeEmbedding.RowSpace (sourceSlots clauses (PreliminarySampler.endpoints questions)) node.val)
        (HierarchicalMatrixTable.other
          (sourceSlots clauses (PreliminarySampler.endpoints questions)) node.val background)
        σ (PrefixTests.nodeDirection rows level node direction).val matrix) := by
  let slots := sourceSlots clauses (PreliminarySampler.endpoints questions)
  have hb : HierarchicalMatrixTable.backgroundOf slots node.val
      (HierarchicalMatrixTable.assemble slots node.val background matrix) = background := by
    funext other row
    exact congrFun (HierarchicalMatrixTable.assemble_other slots node.val background matrix other) row
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact (PrefixMatrixAcceptance.observe_iff_matrix clauses σ questions
    (HierarchicalMatrixTable.assemble slots node.val background matrix) level node direction).trans
    (Iff.of_eq (congrArg₂
      (fun (b : HierarchicalMatrixTable.Background (rows := rows) slots node.val)
        (X : HierarchicalMatrixTable.Matrix (rows := rows) slots node.val) =>
        CanonicalMatrixTable.Accepts (TreeCanonical.numberedSlots slots)
          (NodeEmbedding.RowSpace slots node.val) (HierarchicalMatrixTable.other slots node.val b)
          σ (PrefixTests.nodeDirection rows level node direction).val X)
      hb (HierarchicalMatrixTable.matrix_assemble slots node.val background matrix)))

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev Outer := StoppedProjectedExperiment.Outer (branch := branch) (n := n)
  (j := j) (t := t) (m := m)
abbrev Inner := StoppedProjectedExperiment.Inner (branch := branch) (n := n)
  (i := i) (j := j) (t := t) rows

def upperLevel : Fin n := ⟨j, Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hupper⟩

abbrev chosen (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  StoppedPathHead.child hij (StoppedProjectedExperiment.lowerPath rows hij k)

abbrev continuation (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  StoppedPathHead.tail hij (StoppedProjectedExperiment.lowerPath rows hij k)

theorem stepPath_eq (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    StoppedProjectedExperiment.stoppedPath rows hupper hij o k =
      (StoppedProjectedExperiment.upperPath hupper o).append
        (.step (chosen rows hij k) (continuation rows hij k)) :=
  congrArg (fun p => (StoppedProjectedExperiment.upperPath hupper o).append p)
    (StoppedPathHead.lowerPath_step_eq rows hij k)

def stepTape (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :=
  StoppedOwnInputGeometry.pathTapeEquiv rows repeats
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o sample.1)
    (congrArg (fun p : Path branch n (i + 1) =>
      (⟨i + 1, p⟩ : Σ height, Path branch n height))
      (stepPath_eq rows hupper hij o sample.1)) sample.2

def readout (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :=
  StoppedUsefulPairLaw.readout rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen rows hij sample.1) (continuation rows hij sample.1)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o sample.1)
    (StoppedProjectedExperiment.projection clauses rows hupper hij designated o sample.1)
    (stepTape clauses rows repeats hupper hij designated o sample)

def background (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :=
  StoppedUsefulPairLaw.background rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen rows hij sample.1) (continuation rows hij sample.1)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o sample.1)
    (StoppedProjectedExperiment.projection clauses rows hupper hij designated o sample.1)
    (readout clauses rows repeats hupper hij designated o sample).1

def buckets (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :=
  CutNodeRows.bucketTapeEquiv rows (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (readout clauses rows repeats hupper hij designated o sample).2

def upperDirection (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (direction : PrefixTests.LevelDirection rows (upperLevel hupper)) :=
  PrefixTests.nodeDirection rows (upperLevel hupper)
    ⟨StoppedProjectedExperiment.upper hupper o, StoppedProjectedExperiment.upper_height hupper o⟩
    direction

theorem upperDirection_eq (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (direction : PrefixTests.LevelDirection rows (upperLevel hupper)) :
    upperDirection rows hupper o direction =
      CutNodeRows.directionEquiv rows (StoppedProjectedExperiment.upperPath hupper o) direction := rfl

variable (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev experiment := StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
  hbranch hrows flag σ

def upperEvent (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (x : HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o)) : Bool :=
  PrefixTests.observeAtLevelNode clauses σ o.1
    ((experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).arrays x)
    (upperLevel hupper)
    ⟨StoppedProjectedExperiment.upper hupper o, StoppedProjectedExperiment.upper_height hupper o⟩
    (x.1.2.2 (upperLevel hupper))

theorem arrays_readout (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :
    (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).arrays
        (StoppedProjectedExperiment.tapeRead clauses rows repeats hupper hij designated o sample) =
      HierarchicalMatrixTable.assemble (StoppedProjectedExperiment.nativeSlots clauses o)
        (StoppedProjectedExperiment.upper hupper o)
        (background clauses rows repeats hupper hij designated o sample)
        (BucketMatrixResampling.assembledMatrix
          (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
            (StoppedProjectedExperiment.upper hupper o))
          (rows (Nodes.height (StoppedProjectedExperiment.upper hupper o)))
          (buckets clauses rows repeats hupper hij designated o sample)) := by
  have heval := congrArg
    (ChildBlockProjection.arraysPullback rows
      (StoppedProjectedExperiment.projection clauses rows hupper hij designated o sample.1))
    (StoppedOwnInputGeometry.evaluate_pathTapeEquiv rows repeats
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o sample.1)
      (congrArg (fun p : Path branch n (i + 1) =>
        (⟨i + 1, p⟩ : Σ height, Path branch n height))
        (stepPath_eq rows hupper hij o sample.1)) sample.2)
  have hassemble := StoppedUsefulPairLaw.assembled_arrays rows repeats
    (StoppedProjectedExperiment.upperPath hupper o)
    (chosen rows hij sample.1) (continuation rows hij sample.1)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o sample.1)
    (StoppedProjectedExperiment.projection clauses rows hupper hij designated o sample.1)
    (stepTape clauses rows repeats hupper hij designated o sample)
  exact (StoppedProjectedExperiment.arrays_tapeRead clauses rows repeats hupper hij designated
    hbranch hrows flag σ o sample).trans (heval.symm.trans hassemble.symm)

theorem usefulEvent_eq (κ : ℝ)
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :
    HierarchicalUsefulFamily.usefulEvent
        (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ) κ
        (upperEvent clauses rows repeats hupper hij designated hbranch hrows flag σ)
        ⟨o, StoppedProjectedExperiment.tapeRead clauses rows repeats hupper hij designated o sample⟩ =
      HierarchicalUsefulCollision.usefulAccepted
        (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
        (i + 1)
        (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).original
        (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).arrays
        (HierarchicalAdviceExperiment.lowerEvent
          (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o)) κ σ
        (background clauses rows repeats hupper hij designated o sample)
        (upperDirection rows hupper o (sample.1.2.2 (upperLevel hupper)))
        (buckets clauses rows repeats hupper hij designated o sample) := by
  let S := experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o
  let x := StoppedProjectedExperiment.tapeRead clauses rows repeats hupper hij designated o sample
  let b : HierarchicalMatrixTable.Background (rows := rows) S.slots S.upper :=
    background clauses rows repeats hupper hij designated o sample
  let X : HierarchicalMatrixTable.Matrix (rows := rows) S.slots S.upper :=
    BucketMatrixResampling.assembledMatrix
    (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o))
    (rows (Nodes.height (StoppedProjectedExperiment.upper hupper o)))
    (buckets clauses rows repeats hupper hij designated o sample)
  have harray : S.arrays x = HierarchicalMatrixTable.assemble S.slots S.upper b X :=
    arrays_readout clauses rows repeats hupper hij designated hbranch hrows flag σ o sample
  have hcoarse : HierarchicalAdviceExperiment.coarse S x =
      (⟨b, MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows S.slots S.upper (i + 1) b) X⟩ :
          HierarchicalUsefulness.Coarse S.slots S.upper (i + 1)) :=
    (congrArg (fun arrays : Arrays S.slots rows =>
      HierarchicalUsefulness.observe S.slots S.upper (i + 1) arrays) harray).trans
      (observe_assemble S.slots S.upper (i + 1) b X)
  have htest : upperEvent clauses rows repeats hupper hij designated hbranch hrows flag σ o x =
      decide (CanonicalMatrixTable.Accepts (TreeCanonical.numberedSlots S.slots)
        (NodeEmbedding.RowSpace S.slots S.upper) (HierarchicalMatrixTable.other S.slots S.upper b)
        σ (upperDirection rows hupper o (sample.1.2.2 (upperLevel hupper))).val X) :=
    (congrArg (fun arrays : Arrays S.slots rows =>
      PrefixTests.observeAtLevelNode clauses σ o.1 arrays (upperLevel hupper)
        ⟨StoppedProjectedExperiment.upper hupper o, StoppedProjectedExperiment.upper_height hupper o⟩
        (sample.1.2.2 (upperLevel hupper))) harray).trans
      (upper_observe_assemble clauses σ o.1 (upperLevel hupper)
        ⟨StoppedProjectedExperiment.upper hupper o, StoppedProjectedExperiment.upper_height hupper o⟩
        (sample.1.2.2 (upperLevel hupper)) b X)
  change (upperEvent clauses rows repeats hupper hij designated hbranch hrows flag σ o x &&
    HierarchicalUsefulness.mark S.slots S.upper (i + 1) S.original S.arrays
      (HierarchicalAdviceExperiment.lowerEvent S) κ (HierarchicalAdviceExperiment.coarse S x)) = _
  exact (congrArg₂ (fun accepted marked : Bool => accepted && marked) htest
    (congrArg (HierarchicalUsefulness.mark S.slots S.upper (i + 1) S.original S.arrays
      (HierarchicalAdviceExperiment.lowerEvent S) κ) hcoarse)).trans
    (congrArg (fun marked =>
    decide (CanonicalMatrixTable.Accepts (TreeCanonical.numberedSlots S.slots)
      (NodeEmbedding.RowSpace S.slots S.upper) (HierarchicalMatrixTable.other S.slots S.upper b)
      σ (upperDirection rows hupper o (sample.1.2.2 (upperLevel hupper))).val X) && marked)
    (HierarchicalUsefulness.table_isSome S.slots S.upper (i + 1) S.original S.arrays
      (HierarchicalAdviceExperiment.lowerEvent S) κ σ b
      (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows S.slots S.upper (i + 1) b) X)).symm)

end
end PerfectCompleteness.StoppedProjectedUsefulEvent

end

end OAI
