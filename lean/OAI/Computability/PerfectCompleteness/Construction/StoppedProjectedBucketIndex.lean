import OAI.Computability.PerfectCompleteness.Decoding.CanonicalUpperDirectionSplit
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedExperiment

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedBucketIndex

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

abbrev Base := GeometricCutSplit.Prefix branch (j + 1) (i + 1) ×
  SourceProjectedTag.Tag (branch := branch) (n := i) (t := t)

def baseOf (rows : Nat → Nat)
    (k : StoppedProjectedExperiment.Inner (branch := branch) (n := n)
      (i := i) (j := j) (t := t) rows) : Base (branch := branch) (i := i) (j := j) (t := t) :=
  (k.1, k.2.1)

def withDirections (rows : Nat → Nat)
    (base : Base (branch := branch) (i := i) (j := j) (t := t))
    (directions : CanonicalDirections.Tuple rows n) :
    StoppedProjectedExperiment.Inner (branch := branch) (n := n)
      (i := i) (j := j) (t := t) rows :=
  (base.1, (base.2, directions))

@[simp] theorem baseOf_withDirections (rows : Nat → Nat)
    (base : Base (branch := branch) (i := i) (j := j) (t := t))
    (directions : CanonicalDirections.Tuple rows n) :
    baseOf rows (withDirections rows base directions) = base := rfl

@[simp] theorem withDirections_baseOf (rows : Nat → Nat)
    (k : StoppedProjectedExperiment.Inner (branch := branch) (n := n)
      (i := i) (j := j) (t := t) rows) :
    withDirections rows (baseOf rows k) k.2.2 = k := rfl

def defaultDirections (rows : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1)) :
    CanonicalDirections.Tuple rows n :=
  fun level => Classical.choice
    (PreliminarySampler.directionNonempty (rows (level.val + 1)) (hrows level.val))

def baseLaw (hij : i < j) (hbranch : ∀ k < j + 1, 0 < branch k)
    (flag : Fin (branch i) → FiniteDistribution Bool) :
    FiniteDistribution (Base (branch := branch) (i := i) (j := j) (t := t)) :=
  (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le) hbranch).product
    (SourceProjectedTag.law (t := t) flag)

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

abbrev key (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  withDirections (n := n) rows base (defaultDirections rows hrows)

abbrev Tape (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  WholeArraySampler.Tape rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o (key rows hrows base))
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
      (key rows hrows base))

def tapeLaw (base : Base (branch := branch) (i := i) (j := j) (t := t)) :
    FiniteDistribution (Tape clauses rows repeats hupper hij designated hrows o base) :=
  WholeArraySampler.tapeLaw rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o (key rows hrows base))
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
      (key rows hrows base))

theorem projectedSlots_eq
    (k : StoppedProjectedExperiment.Inner (branch := branch) (n := n)
      (i := i) (j := j) (t := t) rows) :
    StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k =
      StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
        (key rows hrows (baseOf rows k)) := rfl

theorem expectation_coordinate
    (hbranch : ∀ k < j + 1, 0 < branch k)
    (flag : Fin (branch i) → FiniteDistribution Bool) (level : Fin n)
    (f : (base : Base (branch := branch) (i := i) (j := j) (t := t)) →
      PrefixTests.LevelDirection rows level →
      Tape clauses rows repeats hupper hij designated hrows o base → ℝ) :
    (StoppedProjectedExperiment.tapeLaw clauses rows repeats hupper hij designated
      hbranch hrows flag o).expectation
        (fun sample => f (baseOf rows sample.1) (sample.1.2.2 level) sample.2) =
      (baseLaw (t := t) hij hbranch flag).expectation (fun base =>
        (CanonicalDirections.levelLaw rows hrows level).expectation (fun direction =>
          (tapeLaw clauses rows repeats hupper hij designated hrows o base).expectation
            (f base direction))) := by
  rw [StoppedProjectedExperiment.tapeLaw, CandidateCoupling.expectation_sigmaLaw]
  simp only [StoppedProjectedExperiment.innerLaw, baseLaw,
    FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro lowerPrefix
  apply FiniteDistribution.expectation_congr
  intro tag
  exact FiniteProduct.expectation_eval (CanonicalDirections.levelLaw rows hrows) level
    (fun direction =>
      (tapeLaw clauses rows repeats hupper hij designated hrows o (lowerPrefix, tag)).expectation
        (f (lowerPrefix, tag) direction))

end
end PerfectCompleteness.StoppedProjectedBucketIndex

end

end OAI
