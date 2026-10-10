import OAI.Computability.PerfectCompleteness.Sampling.StoppedProjectedGlobalLawLemmas

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedPhysicalAdvice

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

private abbrev physicalSampleFintype
    {branch : Nat → Nat} {n i j t v m : Nat}
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
    (designated : Fin (branch i) → Slots branch i)
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    Fintype (StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o) :=
  inferInstance

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev Outer := StoppedProjectedExperiment.Outer (branch := branch) (n := n)
  (j := j) (t := t) (m := m)

abbrev Advice (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :=
  ManyGoodRows.RowMap (Block rows (StoppedProjectedExperiment.upper hupper o)) r

local instance adviceFintype
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :
    Fintype (Advice rows hupper o r) := linearMapFintype

abbrev Sample (r : Nat) :=
  (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
    (StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o ×
      Advice rows hupper o r)

abbrev RawSample (r : Nat) :=
  (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
    HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o) r

local instance physicalAdviceFintype
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :
    Fintype (StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o ×
      Advice rows hupper o r) := by
  let : Fintype (StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :=
    physicalSampleFintype clauses rows repeats hupper hij designated o
  infer_instance

local instance rawFiberFintype
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :
    Fintype (HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o) r) := by
  let : (A : Advice rows hupper o r) →
      (k : StoppedProjectedExperiment.Inner
        (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) →
      Fintype (OwnInputReference.RawSample
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k) rows
        (StoppedProjectedExperiment.upper hupper o) (StoppedProjectedExperiment.lower rows hupper hij o k)
        (LinearMap.ker A) repeats (StoppedProjectedExperiment.cut rows hupper hij o k)) :=
    fun A k => OwnInputReference.rawSampleFintype
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k) rows
      (StoppedProjectedExperiment.upper hupper o) (StoppedProjectedExperiment.lower rows hupper hij o k)
      (LinearMap.ker A) repeats (StoppedProjectedExperiment.cut rows hupper hij o k)
  let : (A : Advice rows hupper o r) →
      Fintype ((k : StoppedProjectedExperiment.Inner
        (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) ×
        OwnInputReference.RawSample
          (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k) rows
          (StoppedProjectedExperiment.upper hupper o) (StoppedProjectedExperiment.lower rows hupper hij o k)
          (LinearMap.ker A) repeats (StoppedProjectedExperiment.cut rows hupper hij o k)) :=
    fun _ => Sigma.instFintype
  exact Sigma.instFintype

def read (r : Nat) (sample : Sample (t := t) clauses rows repeats hupper hij designated r) :
    RawSample (t := t) clauses rows repeats hupper hij designated r :=
  ⟨sample.1, HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated sample.1)
    (StoppedProjectedExperiment.upper hupper sample.1)
    (StoppedProjectedExperiment.lower rows hupper hij sample.1)
    (StoppedProjectedExperiment.cut rows hupper hij sample.1) r
    (StoppedProjectedExperiment.physicalExperimentRead clauses rows repeats hupper hij designated
      sample.1 sample.2.1, sample.2.2)⟩

variable [NeZero m]
  (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

def law (r : Nat) : FiniteDistribution (Sample (t := t) clauses rows repeats hupper hij designated r) :=
  CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (fun o => (StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o).product
        (FiniteDistribution.uniform (Advice rows hupper o r)))

def rawLaw (r : Nat) : FiniteDistribution (RawSample (t := t) clauses rows repeats hupper hij designated r) :=
  CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (fun o => HierarchicalProjectedExperiment.rawLaw (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o)
      (StoppedProjectedExperiment.innerLaw rows hij
        (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag) r)

include σ

omit [NeZero m] in
theorem fiber_read_law
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :
    ((StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
        (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o).product
      (FiniteDistribution.uniform (Advice rows hupper o r))).pushforward
        (fun x => HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
          (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
          (StoppedProjectedExperiment.upper hupper o)
          (StoppedProjectedExperiment.lower rows hupper hij o)
          (StoppedProjectedExperiment.cut rows hupper hij o) r
          (StoppedProjectedExperiment.physicalExperimentRead
            clauses rows repeats hupper hij designated o x.1, x.2)) =
      HierarchicalProjectedExperiment.rawLaw (rows := rows) (repeats := repeats)
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o)
        (StoppedProjectedExperiment.cut rows hupper hij o)
        (StoppedProjectedExperiment.innerLaw rows hij
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag) r := by
  let μ := StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o
  let ν := FiniteDistribution.uniform (Advice rows hupper o r)
  let readTape := StoppedProjectedExperiment.physicalExperimentRead
    clauses rows repeats hupper hij designated o
  let readRaw := HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
    (StoppedProjectedExperiment.upper hupper o)
    (StoppedProjectedExperiment.lower rows hupper hij o)
    (StoppedProjectedExperiment.cut rows hupper hij o) r
  have hprod := FiniteDistribution.product_pushforward μ ν readTape (id : Advice rows hupper o r → _)
  rw [FiniteDistribution.pushforward_id] at hprod
  have hcomp := FiniteDistribution.pushforward_comp (μ.product ν)
    (fun x => (readTape x.1, (id : Advice rows hupper o r → _) x.2)) readRaw
  have hphysical := StoppedProjectedExperiment.physicalExperimentRead_law
    clauses rows repeats hupper hij designated
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag σ o
  change μ.pushforward readTape = _ at hphysical
  have hraw := HierarchicalProjectedExperiment.rawRead_law (rows := rows) (repeats := repeats)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
    (StoppedProjectedExperiment.upper hupper o)
    (StoppedProjectedExperiment.lower rows hupper hij o)
    (StoppedProjectedExperiment.cut rows hupper hij o)
    (StoppedProjectedExperiment.innerLaw rows hij
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag) r
  have hprodRaw := congrArg
    (fun P : FiniteDistribution
      (HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o)
        (StoppedProjectedExperiment.cut rows hupper hij o) × Advice rows hupper o r) =>
      P.pushforward readRaw) hprod
  have hphysicalRaw := congrArg
    (fun P : FiniteDistribution
      (HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o)
        (StoppedProjectedExperiment.cut rows hupper hij o)) =>
      (P.product ν).pushforward readRaw) hphysical
  exact hcomp.symm.trans (hprodRaw.trans (hphysicalRaw.trans hraw))

theorem read_law (r : Nat) :
    (law (t := t) clauses rows repeats hupper hij designated hbranch hrows flag r).pushforward
        (read (t := t) clauses rows repeats hupper hij designated r) =
      rawLaw (t := t) clauses rows repeats hupper hij designated hbranch hrows flag r := by
  have hsplit := SigmaObservation.pushforward_fiber
    (X := fun o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m) =>
      StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o ×
        Advice rows hupper o r)
    (Y := fun o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m) =>
      HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o)
        (StoppedProjectedExperiment.cut rows hupper hij o) r)
    (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (fun o => (StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o).product
        (FiniteDistribution.uniform (Advice rows hupper o r)))
    (fun o x => HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o) r
      (StoppedProjectedExperiment.physicalExperimentRead
        clauses rows repeats hupper hij designated o x.1, x.2))
  exact hsplit.trans (congrArg
    (CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch))
    (funext (fun o => fiber_read_law clauses rows repeats hupper hij designated
      hbranch hrows flag σ o r)))

theorem expectation_read (r : Nat)
    (value : RawSample (t := t) clauses rows repeats hupper hij designated r → ℝ) :
    (law clauses rows repeats hupper hij designated hbranch hrows flag r).expectation
        (fun sample => value (read clauses rows repeats hupper hij designated r sample)) =
      (rawLaw clauses rows repeats hupper hij designated hbranch hrows flag r).expectation value := by
  rw [← read_law clauses rows repeats hupper hij designated hbranch hrows flag σ r]
  exact (FiniteDistribution.expectation_pushforward _ _ _).symm

end
end PerfectCompleteness.StoppedProjectedPhysicalAdvice

end

end OAI
