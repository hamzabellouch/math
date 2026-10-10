import OAI.Computability.PerfectCompleteness.Decoding.CutProjectionAssembly
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedExperimentLemmas
import OAI.Computability.PerfectCompleteness.Foundations.SourceProjectedTag
import OAI.Computability.PerfectCompleteness.Machines.SourcePhysicalTapeLaw
import OAI.Computability.PerfectCompleteness.Machines.StoppedOwnInputGeometry

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedExperiment

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RelativeDescendantProducts
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

theorem below_append (hij : i < j) : {n : Nat} → (p : Path branch n (j + 1)) →
    (q : Path branch (j + 1) (i + 1)) →
    Below branch (WholeArrayInteriorExterior.upperNode p)
      (WholeArrayInteriorExterior.upperNode (p.append q))
  | _, .refl _, q => by
      cases q with
      | refl => omega
      | step child q => exact Below.root child (WholeArrayInteriorExterior.upperNode q)
  | _, .step child p, q => Below.child child (below_append hij p q)

abbrev Outer := PreliminarySampler.Questions branch n t m ×
  GeometricCutSplit.Prefix branch n (j + 1)

abbrev Inner (rows : Nat → Nat) :=
  GeometricCutSplit.Prefix branch (j + 1) (i + 1) ×
    (SourceProjectedTag.Tag (branch := branch) (n := i) (t := t) ×
      CanonicalDirections.Tuple rows n)

def outerLaw [NeZero m] (hupper : j + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) :
    FiniteDistribution (Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  PreliminarySampler.questionsLaw.product (GeometricCutSplit.prefixLaw hupper hbranch)

def innerLaw (rows : Nat → Nat) (hij : i < j)
    (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (flag : Fin (branch i) → FiniteDistribution Bool) :
    FiniteDistribution (Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le) hbranch).product
    ((SourceProjectedTag.law (t := t) flag).product (CanonicalDirections.law rows n hrows))

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev nativeSlots (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  sourceSlots clauses (PreliminarySampler.endpoints o.1)

def upperPath (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  GeometricCutSplit.prefixPath hupper o.2

def lowerPath (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) k.1

def stoppedPath (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  (upperPath hupper o).append (lowerPath rows hij k)

def upper (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  WholeArrayInteriorExterior.upperNode (upperPath hupper o)

def lower (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  WholeArrayInteriorExterior.upperNode (stoppedPath rows hupper hij o k)

@[simp] theorem upper_height (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    Nodes.height (upper hupper o) = j + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

@[simp] theorem lower_height (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Nodes.height (lower rows hupper hij o k) = i + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

def cut (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    OwnInputReference.Cut (upper hupper o) (lower rows hupper hij o k) :=
  StoppedOwnInputGeometry.cutOfBelow (below_append hij (upperPath hupper o) (lowerPath rows hij k))

theorem fullPath_spec (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    (⟨Nodes.height (lower rows hupper hij o k),
      WholeArrayInteriorOwnInputLaw.fullPath (upper hupper o) (lower rows hupper hij o k)
        (cut rows hupper hij o k)⟩ : Σ height, Path branch n height) =
      ⟨i + 1, stoppedPath rows hupper hij o k⟩ := by
  have hpath :
      WholeArrayInteriorOwnInputLaw.fullPath (upper hupper o) (lower rows hupper hij o k)
        (cut rows hupper hij o k) = Nodes.path (lower rows hupper hij o k) :=
    StoppedOwnInputGeometry.fullPath_cutOfBelow
      (below_append hij (upperPath hupper o) (lowerPath rows hij k))
  exact (congrArg (fun path : Path branch n (Nodes.height (lower rows hupper hij o k)) =>
    (⟨Nodes.height (lower rows hupper hij o k), path⟩ : Σ height, Path branch n height))
      hpath).trans
    (WholeArrayInteriorExterior.upperNode_spec (stoppedPath rows hupper hij o k))

def cutQuestions (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    PreliminarySampler.Questions branch (i + 1) t m :=
  fun leaf a => o.1 ((stoppedPath rows hupper hij o k).slotEmbedding leaf) a

def projectedSlots (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill (stoppedPath rows hupper hij o k) (nativeSlots clauses o)
    (SourceProjectedTag.mixedInside clauses designated (cutQuestions rows hupper hij o k)
      k.2.1.1 k.2.1.2)

theorem fill_native (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    CutSlotAssembly.fill (stoppedPath rows hupper hij o k) (nativeSlots clauses o)
      (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o k)) =
      nativeSlots clauses o :=
  CutSlotAssembly.fill_restrict (stoppedPath rows hupper hij o k) (nativeSlots clauses o)

def projection (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    ∀ leaf a, MixedSupport.Projection (nativeSlots clauses o leaf a)
      (projectedSlots clauses rows hupper hij designated o k leaf a) :=
  fun leaf a => CutProjectionAssembly.castProjection
    (congrFun (congrFun (fill_native clauses rows hupper hij o k) leaf) a) rfl
    (CutProjectionAssembly.fillProjection (stoppedPath rows hupper hij o k) (nativeSlots clauses o)
      (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o k))
      (SourceProjectedTag.mixedInside clauses designated (cutQuestions rows hupper hij o k)
        k.2.1.1 k.2.1.2)
      (SourceProjectedTag.projection clauses designated (cutQuestions rows hupper hij o k)
        k.2.1.1 k.2.1.2) leaf a)

def direction (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Block rows (lower rows hupper hij o k) :=
  let level : Fin n := ⟨i, Nat.lt_of_lt_of_le (Nat.lt_trans hij (Nat.lt_succ_self j)) hupper⟩
  (PrefixTests.nodeDirection rows level
    ⟨lower rows hupper hij o k, lower_height rows hupper hij o k⟩ (k.2.2 level)).val

variable (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev experiment (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  HierarchicalProjectedExperiment.experiment (rows := rows) (repeats := repeats)
    (nativeSlots clauses o) (projectedSlots clauses rows hupper hij designated o)
    (projection clauses rows hupper hij designated o) (upper hupper o) (i + 1)
    (lower rows hupper hij o) (cut rows hupper hij o) (direction rows hupper hij o)
    (innerLaw rows hij hbranch hrows flag) σ

abbrev TapeSample (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) ×
    WholeArraySampler.Tape rows repeats (stoppedPath rows hupper hij o k)
      (projectedSlots clauses rows hupper hij designated o k)

def tapeLaw (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    FiniteDistribution (TapeSample clauses rows repeats hupper hij designated o) :=
  CompletionSoundness.sigmaLaw (innerLaw rows hij hbranch hrows flag) (fun k =>
    WholeArraySampler.tapeLaw rows repeats (stoppedPath rows hupper hij o k)
      (projectedSlots clauses rows hupper hij designated o k))

def tapeRead (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : TapeSample clauses rows repeats hupper hij designated o) :
    HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (projectedSlots clauses rows hupper hij designated o) (upper hupper o)
      (lower rows hupper hij o) (cut rows hupper hij o) :=
  ⟨sample.1, StoppedOwnInputGeometry.pathTapeEquiv rows repeats
    (projectedSlots clauses rows hupper hij designated o sample.1)
    (fullPath_spec rows hupper hij o sample.1).symm sample.2⟩

theorem tapeRead_law (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    (tapeLaw clauses rows repeats hupper hij designated hbranch hrows flag o).pushforward
        (tapeRead clauses rows repeats hupper hij designated o) =
      (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).original := by
  calc
    _ = CompletionSoundness.sigmaLaw (innerLaw rows hij hbranch hrows flag) (fun k =>
        (WholeArraySampler.tapeLaw rows repeats (stoppedPath rows hupper hij o k)
          (projectedSlots clauses rows hupper hij designated o k)).pushforward
            (StoppedOwnInputGeometry.pathTapeEquiv rows repeats
              (projectedSlots clauses rows hupper hij designated o k)
              (fullPath_spec rows hupper hij o k).symm)) :=
      SigmaObservation.pushforward_fiber (innerLaw rows hij hbranch hrows flag)
        (fun k => WholeArraySampler.tapeLaw rows repeats (stoppedPath rows hupper hij o k)
          (projectedSlots clauses rows hupper hij designated o k))
        (fun k tape => StoppedOwnInputGeometry.pathTapeEquiv rows repeats
          (projectedSlots clauses rows hupper hij designated o k)
          (fullPath_spec rows hupper hij o k).symm tape)
    _ = _ :=
      congrArg (fun kernel :
          (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) →
            FiniteDistribution (WholeArraySampler.Tape rows repeats
              (WholeArrayInteriorOwnInputLaw.fullPath (upper hupper o)
                (lower rows hupper hij o k) (cut rows hupper hij o k))
              (projectedSlots clauses rows hupper hij designated o k)) =>
        CompletionSoundness.sigmaLaw (innerLaw rows hij hbranch hrows flag) kernel)
        (funext (fun k => StoppedOwnInputGeometry.pathTapeEquiv_law rows repeats
          (projectedSlots clauses rows hupper hij designated o k)
          (fullPath_spec rows hupper hij o k).symm))

theorem arrays_tapeRead (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : TapeSample clauses rows repeats hupper hij designated o) :
    (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).arrays
        (tapeRead clauses rows repeats hupper hij designated o sample) =
      ChildBlockProjection.arraysPullback rows
        (projection clauses rows hupper hij designated o sample.1)
        (WholeArraySampler.evaluate rows repeats (stoppedPath rows hupper hij o sample.1)
          (projectedSlots clauses rows hupper hij designated o sample.1) sample.2) :=
  congrArg (ChildBlockProjection.arraysPullback rows
    (projection clauses rows hupper hij designated o sample.1))
    (StoppedOwnInputGeometry.evaluate_pathTapeEquiv rows repeats
      (projectedSlots clauses rows hupper hij designated o sample.1)
      (fullPath_spec rows hupper hij o sample.1).symm sample.2)

section Physical

variable [NeZero m]

abbrev PhysicalBase :=
  GeometricCutSplit.Prefix branch (j + 1) (i + 1) ×
    (SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t) ×
      CanonicalDirections.Tuple rows n)

def withFlags (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows)
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i)) :
    Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows :=
  (base.1, ((base.2.1, flags), base.2.2))

def physicalBaseLaw :
    FiniteDistribution (PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le) hbranch).product
    ((SourceProjectedTag.positionLaw (branch := branch) (n := i) (t := t)).product
      (CanonicalDirections.law rows n hrows))

abbrev baseTag (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  withFlags rows base (fun _ => false)

def physicalSources (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  SourceQuestionKernelJoint.sources designated
    (cutQuestions rows hupper hij o (baseTag rows base)) base.2.1

abbrev PhysicalRaw (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  SourcePhysicalWholeLaw.Raw rows repeats (stoppedPath rows hupper hij o (baseTag rows base))
    (nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o (baseTag rows base)))
    clauses designated

abbrev PhysicalSample (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) ×
    PhysicalRaw clauses rows repeats hupper hij designated o base

def physicalFiberLaw (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    FiniteDistribution (PhysicalRaw clauses rows repeats hupper hij designated o base) :=
  SourcePhysicalWholeLaw.rawLaw rows repeats (stoppedPath rows hupper hij o (baseTag rows base))
    (nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o (baseTag rows base)))
    clauses designated flag (physicalSources rows hupper hij designated o base)

def physicalLaw (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    FiniteDistribution (PhysicalSample clauses rows repeats hupper hij designated o) :=
  CompletionSoundness.sigmaLaw (physicalBaseLaw rows hij hbranch hrows)
    (physicalFiberLaw clauses rows repeats hupper hij designated flag o)

def physicalRead (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : PhysicalSample clauses rows repeats hupper hij designated o) :
    TapeSample clauses rows repeats hupper hij designated o :=
  let observed := SourcePhysicalTapeLaw.observeFiber rows repeats
    (stoppedPath rows hupper hij o (baseTag rows sample.1)) (nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o (baseTag rows sample.1)))
    clauses designated (physicalSources rows hupper hij designated o sample.1) sample.2
  ⟨withFlags rows sample.1 observed.1, observed.2⟩

omit [NeZero m] in
theorem physicalFiber_probability
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows)
    (event : TapeSample clauses rows repeats hupper hij designated o → Bool) :
    (physicalFiberLaw clauses rows repeats hupper hij designated flag o base).probability
        (fun raw => event (physicalRead clauses rows repeats hupper hij designated o ⟨base, raw⟩)) =
      (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
        (WholeArraySampler.tapeLaw rows repeats
          (stoppedPath rows hupper hij o (withFlags rows base flags))
          (projectedSlots clauses rows hupper hij designated o (withFlags rows base flags))).probability
            (fun tape => event ⟨withFlags rows base flags, tape⟩)) := by
  have hlaw := SourcePhysicalTapeLaw.observeFiber_law rows repeats
    (stoppedPath rows hupper hij o (baseTag rows base)) (nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o (baseTag rows base)))
    clauses designated flag (physicalSources rows hupper hij designated o base)
  have h := congrArg (fun μ : FiniteDistribution
      ((flags : SourceProjectedTag.Flags (branch := branch) (n := i)) ×
        WholeArraySampler.Tape rows repeats
          (stoppedPath rows hupper hij o (withFlags rows base flags))
          (projectedSlots clauses rows hupper hij designated o (withFlags rows base flags))) =>
    μ.probability (fun observed =>
    event (⟨withFlags rows base observed.1, observed.2⟩ :
      TapeSample clauses rows repeats hupper hij designated o))) hlaw
  have hp := FiniteDistribution.probability_pushforward
    (Ω := PhysicalRaw clauses rows repeats hupper hij designated o base)
    (Γ := ((flags : SourceProjectedTag.Flags (branch := branch) (n := i)) ×
      WholeArraySampler.Tape rows repeats
        (stoppedPath rows hupper hij o (withFlags rows base flags))
        (projectedSlots clauses rows hupper hij designated o (withFlags rows base flags))))
    (physicalFiberLaw clauses rows repeats hupper hij designated flag o base)
    (SourcePhysicalTapeLaw.observeFiber rows repeats
      (stoppedPath rows hupper hij o (baseTag rows base)) (nativeSlots clauses o)
      (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o (baseTag rows base)))
      clauses designated (physicalSources rows hupper hij designated o base))
    (fun observed => event ⟨withFlags rows base observed.1, observed.2⟩)
  have hs := CompletionSoundness.sigmaLaw_probability (SourceProjectedTag.flagLaw flag)
    (fun flags => WholeArraySampler.tapeLaw rows repeats
      (stoppedPath rows hupper hij o (withFlags rows base flags))
      (projectedSlots clauses rows hupper hij designated o (withFlags rows base flags)))
    (fun observed => event ⟨withFlags rows base observed.1, observed.2⟩)
  exact hp.symm.trans (h.trans hs)

omit [NeZero m] in
theorem physicalRead_law
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    (physicalLaw clauses rows repeats hupper hij designated hbranch hrows flag o).pushforward
        (physicalRead clauses rows repeats hupper hij designated o) =
      tapeLaw clauses rows repeats hupper hij designated hbranch hrows flag o := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, physicalLaw,
    CompletionSoundness.sigmaLaw_probability, tapeLaw, CompletionSoundness.sigmaLaw_probability]
  simp only [physicalBaseLaw, innerLaw, SourceProjectedTag.law,
    FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro pref
  apply FiniteDistribution.expectation_congr
  intro positions
  calc
    _ = (CanonicalDirections.law rows n hrows).expectation (fun directions =>
        (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
          (WholeArraySampler.tapeLaw rows repeats
            (stoppedPath rows hupper hij o (withFlags rows (pref, (positions, directions)) flags))
            (projectedSlots clauses rows hupper hij designated o
              (withFlags rows (pref, (positions, directions)) flags))).probability
                (fun tape => event ⟨withFlags rows (pref, (positions, directions)) flags, tape⟩))) := by
      apply FiniteDistribution.expectation_congr
      intro directions
      exact physicalFiber_probability clauses rows repeats hupper hij designated flag o
        (pref, (positions, directions)) event
    _ = _ := FiniteDistribution.expectation_comm _ _ _

def physicalExperimentRead
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : PhysicalSample clauses rows repeats hupper hij designated o) :=
  tapeRead clauses rows repeats hupper hij designated o
    (physicalRead clauses rows repeats hupper hij designated o sample)

omit [NeZero m] in
theorem physicalExperimentRead_law
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    (physicalLaw clauses rows repeats hupper hij designated hbranch hrows flag o).pushforward
        (physicalExperimentRead clauses rows repeats hupper hij designated o) =
      (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).original := by
  change (physicalLaw clauses rows repeats hupper hij designated hbranch hrows flag o).pushforward
    (fun sample => tapeRead clauses rows repeats hupper hij designated o
      (physicalRead clauses rows repeats hupper hij designated o sample)) = _
  rw [← FiniteDistribution.pushforward_comp, physicalRead_law]
  exact tapeRead_law clauses rows repeats hupper hij designated hbranch hrows flag σ o

end Physical

end
end PerfectCompleteness.StoppedProjectedExperiment

end

end OAI
