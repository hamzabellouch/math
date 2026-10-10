import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionPairPullback
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionPhysicalHigh
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionRawSwap
import OAI.Computability.PerfectCompleteness.Decoding.SourceQuestionCollisionTransportLemmas
import OAI.Computability.PerfectCompleteness.Decoding.SourceQuestionTaggedProjection

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPhysicalCollision

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)
  (q : SourceQuestionLowerForms.Questions
    (branch := branch) (height := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple
    (branch := branch) (n := height) (t := t))
  (direction : BucketSampler.Direction (rows (height + 1)))
  (cutoff : Nat)
  (table : SourceQuestionLowerForms.UpperTable (rows := rows)
    path outside clauses upper level (adviceRows := adviceRows) q)

def rawEvent (flags : SourceProjectedTag.Flags (branch := branch) (n := height))
    (raw : CutChildGrouping.Raw
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      (SourceProjectedTag.mixedInside clauses designated q choices flags) rows) : Bool :=
  LowerProjectedFiberAverage.collision
    (SourceQuestionPhysicalHigh.originalSlots path outside clauses q)
    (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)
    (SourceQuestionPhysicalHigh.projection path outside clauses designated q choices flags)
    upper level hbranch d A cutoff table
    (LowerCutPair.arraysPair rows repeats path
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)
      (SourceQuestionPhysicalHigh.exteriorAt path outside placeholder clauses designated
        q choices flags exterior) direction
      (SourceQuestionPairPullback.rawAtCut rows repeats path outside
        (SourceProjectedTag.mixedInside clauses designated q choices flags) raw))

theorem collision_eq_probability
    (flags : SourceProjectedTag.Flags (branch := branch) (n := height)) :
    SourceQuestionPhysicalHigh.collision path outside placeholder clauses designated
        q choices flags upper level d hbranch A exterior direction cutoff table =
      (CutChildGrouping.rawLaw
        (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).probability
          (rawEvent path outside placeholder clauses designated upper level d hbranch A exterior
            q choices direction cutoff table flags) := by
  let event : LowerCutPair.Raw rows repeats path
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags) →
      Bool := fun raw =>
    LowerProjectedFiberAverage.collision
      (SourceQuestionPhysicalHigh.originalSlots path outside clauses q)
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)
      (SourceQuestionPhysicalHigh.projection path outside clauses designated q choices flags)
      upper level hbranch d A cutoff table
      (LowerCutPair.arraysPair rows repeats path
        (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)
        (SourceQuestionPhysicalHigh.exteriorAt path outside placeholder clauses designated
          q choices flags exterior) direction raw)
  have hlaw :
      (CutChildGrouping.rawLaw
        (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).pushforward
          (SourceQuestionPairPullback.rawAtCut rows repeats path outside
            (SourceProjectedTag.mixedInside clauses designated q choices flags)) =
        CutChildGrouping.rawLaw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (WholeCutGrouping.cutSlots path
            (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated
              q choices flags)) rows :=
    SourceQuestionLowerForms.rawCast_law rows
      (CleanPhysicalReplay.cutSlots_fill path outside
        (SourceProjectedTag.mixedInside clauses designated q choices flags)).symm
  exact (congrArg (fun μ : FiniteDistribution (LowerCutPair.Raw rows repeats path
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)) =>
        μ.probability event) hlaw).symm.trans
    (FiniteDistribution.probability_pushforward _ _ event)

theorem flags_collision_eq_kernels
    (flag : Fin (branch height) → FiniteDistribution Bool) :
    (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
      SourceQuestionPhysicalHigh.collision path outside placeholder clauses designated
        q choices flags upper level d hbranch A exterior direction cutoff table) =
      (SourceQuestionRawSwap.kernelLaw
        (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
        rows clauses designated flag q choices).probability (fun raw =>
          let observed := SourcePhysicalTaggedChildren.observe rows clauses designated
            (SourceQuestionKernelJoint.sources designated q choices) raw
          rawEvent path outside placeholder clauses designated upper level d hbranch A exterior
            q choices direction cutoff table observed.1 observed.2) := by
  let event :
      (Σ flags : SourceProjectedTag.Flags (branch := branch) (n := height),
        CutChildGrouping.Raw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (SourcePhysicalTaggedChildren.slots clauses designated
            (SourceQuestionKernelJoint.sources designated q choices) flags) rows) → Bool :=
    fun observed => rawEvent path outside placeholder clauses designated upper level d hbranch A
      exterior q choices direction cutoff table observed.1 observed.2
  have h := congrArg (fun μ : FiniteDistribution
      (Σ flags : SourceProjectedTag.Flags (branch := branch) (n := height),
        CutChildGrouping.Raw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (SourcePhysicalTaggedChildren.slots clauses designated
            (SourceQuestionKernelJoint.sources designated q choices) flags) rows) =>
      μ.probability event)
    (SourcePhysicalTaggedChildren.kernels_tagged
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      rows clauses designated flag (SourceQuestionKernelJoint.sources designated q choices))
  have hpush := FiniteDistribution.probability_pushforward
    (FiniteProduct.law (fun i => SourceChildKernel.kernel
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      rows clauses designated flag i (SourceQuestionKernelJoint.sources designated q choices i)))
    (SourcePhysicalTaggedChildren.observe rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices)) event
  have hsigma := CompletionSoundness.sigmaLaw_probability (FiniteProduct.law flag)
    (fun flags => CutChildGrouping.rawLaw
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      (SourcePhysicalTaggedChildren.slots clauses designated
        (SourceQuestionKernelJoint.sources designated q choices) flags) rows) event
  calc
    _ = (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
        (CutChildGrouping.rawLaw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).probability
            (rawEvent path outside placeholder clauses designated upper level d hbranch A exterior
              q choices direction cutoff table flags)) := by
      apply FiniteDistribution.expectation_congr
      intro flags
      exact collision_eq_probability path outside placeholder clauses designated upper level d
        hbranch A exterior q choices direction cutoff table flags
    _ = _ := (hpush.symm.trans (h.trans hsigma)).symm

variable
  (tables : (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m)) →
    SourceQuestionLowerForms.UpperTable (rows := rows)
      path outside clauses upper level (adviceRows := adviceRows) q)

theorem rawEvent_observe
    (raw : SourceChildKernelJoint.RawTuple
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      (t := t) rows clauses designated) :
    let observed := SourcePhysicalTaggedChildren.observe rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw
    rawEvent path outside placeholder clauses designated upper level d hbranch A exterior
        q choices direction cutoff (tables q) observed.1 observed.2 =
      SourceQuestionCollisionTransport.globalRestricted path outside placeholder clauses
        upper level d hbranch A exterior tables cutoff designated q choices raw direction := by
  let observed :
      Σ flags : SourceProjectedTag.Flags (branch := branch) (n := height),
        CutChildGrouping.Raw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (SourceProjectedTag.mixedInside clauses designated q choices flags) rows :=
    SourcePhysicalTaggedChildren.observe rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw
  let first : SourceQuestionLowerForms.Raw (rows := rows) (repeats := repeats) path clauses q →
      Arrays (SourceQuestionLowerForms.slots path outside clauses q) rows := fun record =>
    LowerCutPair.first rows repeats path (SourceQuestionLowerForms.slots path outside clauses q)
      (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
        (SourceChildMarkedLaw.questionSlots clauses q) exterior)
      (SourceQuestionLowerForms.rawAtCut path outside clauses q record)
  let second : SourceQuestionLowerForms.Raw (rows := rows) (repeats := repeats) path clauses q →
      Arrays (SourceQuestionLowerForms.slots path outside clauses q) rows := fun record =>
    LowerCutPair.second rows repeats path (SourceQuestionLowerForms.slots path outside clauses q)
      (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
        (SourceChildMarkedLaw.questionSlots clauses q) exterior) direction
      (SourceQuestionLowerForms.rawAtCut path outside clauses q record)
  let read : Arrays (SourceQuestionLowerForms.slots path outside clauses q) rows →
      Option (BilinearCollisionTransfer.Form (𝕜 := F2)
        (H := HierarchicalDecoderTables.LowerH
          (SourceQuestionLowerForms.slots path outside clauses q) upper level d)) := fun arrays =>
    (LowerCutDecoderForm.answer (SourceQuestionLowerForms.slots path outside clauses q)
      upper level d hbranch A (tables q) cutoff arrays).map
        (OddListExtraction.multiplicationForm (HierarchicalDecoderTables.LowerH
          (SourceQuestionLowerForms.slots path outside clauses q) upper level d))
  have hfirst := SourceQuestionPairPullback.first_pullback rows repeats path outside placeholder
    (SourceChildMarkedLaw.questionSlots clauses q)
    (SourceProjectedTag.mixedInside clauses designated q choices observed.1)
    (SourceProjectedTag.projection clauses designated q choices observed.1)
    exterior observed.2
  have hsecond := SourceQuestionPairPullback.second_pullback rows repeats path outside placeholder
    (SourceChildMarkedLaw.questionSlots clauses q)
    (SourceProjectedTag.mixedInside clauses designated q choices observed.1)
    (SourceProjectedTag.projection clauses designated q choices observed.1)
    exterior direction observed.2
  have hrecord : (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2 =
      ChildAssemblyProjection.rawPullback rows
        (SourceProjectedTag.projection clauses designated q choices observed.1) observed.2 :=
    SourceQuestionTaggedProjection.markedBlocks_snd rows clauses designated q choices raw
  have hfirstForm := congrArg read (hfirst.trans (congrArg first hrecord.symm))
  have hsecondForm := congrArg read (hsecond.trans (congrArg second hrecord.symm))
  have hinside : SourceProjectedTag.projection clauses designated q choices observed.1 =
      SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw :=
    SourceQuestionTaggedProjection.projection_observe rows clauses designated q choices raw
  have hprojection :
      SourceQuestionPhysicalHigh.projection path outside clauses designated q choices observed.1 =
        SourceQuestionCollisionTransport.projection path outside clauses designated q choices raw :=
    congrArg (CutProjectionAssembly.fillProjection path outside
      (SourceChildMarkedLaw.questionSlots clauses q)
      (SourceProjectedTag.mixedInside clauses designated q choices observed.1)) hinside
  have hspace := congrArg (fun projection : ∀ leaf j, MixedSupport.Projection
      (SourceQuestionLowerForms.slots path outside clauses q leaf j)
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated
        q choices observed.1 leaf j) =>
    LinearMap.range (HPullback (ChildBlockProjection.nodeProjection projection
      (HierarchicalLeftDecoder.LowerNode upper level d)))) hprojection
  exact congrArg₂ (fun (pair : _ × _) space =>
    BilinearCollisionTransfer.restrictedCollision pair.1 pair.2 space)
    (congrArg₂ Prod.mk hfirstForm hsecondForm) hspace

theorem mean_collision_eq
    (flag : Fin (branch height) → FiniteDistribution Bool) :
    (SourceProjectedTag.positionLaw (branch := branch) (n := height) (t := t)).expectation
      (fun choices => (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
        SourceQuestionPhysicalHigh.collision path outside placeholder clauses designated
          q choices flags upper level d hbranch A exterior direction cutoff (tables q))) =
      (SourceProjectedTag.positionLaw (branch := branch) (n := height) (t := t)).expectation
        (fun choices => (SourceQuestionRawSwap.kernelLaw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          rows clauses designated flag q choices).probability (fun raw =>
            SourceQuestionCollisionTransport.globalRestricted path outside placeholder clauses
              upper level d hbranch A exterior tables cutoff designated q choices raw direction)) := by
  apply FiniteDistribution.expectation_congr
  intro choices
  rw [flags_collision_eq_kernels path outside placeholder clauses designated upper level d
    hbranch A exterior q choices direction cutoff (tables q) flag]
  apply congrArg (fun event => (SourceQuestionRawSwap.kernelLaw
    (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
    rows clauses designated flag q choices).probability event)
  funext raw
  exact rawEvent_observe path outside placeholder clauses designated upper level d hbranch A
    exterior q choices direction cutoff tables raw

end
end PerfectCompleteness.SourceQuestionPhysicalCollision

end

end OAI
