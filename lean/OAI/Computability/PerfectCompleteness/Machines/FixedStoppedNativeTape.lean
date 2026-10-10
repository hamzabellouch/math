import OAI.Computability.PerfectCompleteness.Decoding.FixedStoppedNativeProjection
import OAI.Computability.PerfectCompleteness.Foundations.SourcePhysicalExteriorReplay
import OAI.Computability.PerfectCompleteness.Machines.StoppedCleanOwnInputGeometry
import OAI.Computability.PerfectCompleteness.Repetition.StoppedCleanCutEquality

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedNativeTape

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open FixedStoppedPhysicalLaw (clauses designated)
open FixedStoppedNativeProjection (physicalSample innerTag path childSample)

private theorem cast_trans_toFun_heq {α β γ : Type}
    (h : α = β) (e : β ≃ γ)
    (he : ∀ b : β, HEq (@Equiv.toFun β γ e b) b) (a : α) :
    HEq (@Equiv.toFun α γ ((Equiv.cast h).trans e) a) a := by
  cases h
  exact he a

section Transport

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

omit [NeZero m] in
private theorem observeFiber_tape_heq
    (p : Path branch root (h + 1))
    (outside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (x : CleanPhysicalReplay.Sample (t := t) rows repeats p clauses designated)
    (hs : sources = SourcePhysicalTapeLaw.sourceTag rows repeats p clauses designated x)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    HEq (SourcePhysicalTapeLaw.observeFiber rows repeats p outside placeholder clauses designated
        sources (external, SourceQuestionRawSwap.raw rows clauses designated x)).2
      (WholeCutSampler.collapse rows repeats p
        (CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated
          x external)) := by
  cases hs
  rfl

omit [NeZero m] in
private theorem collapsedRightTape_heq
    {p q : Path branch root (h + 1)} (hp : p = q)
    (outside otherOutside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder otherPlaceholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (x : CleanPhysicalReplay.Sample (t := t) rows repeats p clauses designated)
    (y : CleanPhysicalReplay.Sample (t := t) rows repeats q clauses designated)
    (hx : HEq x y)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (other : CleanPhysicalReplay.Exterior rows repeats q otherOutside otherPlaceholder)
    (hext : HEq external other)
    (hslots : CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated x =
      CleanPhysicalCanonicalQuery.rightSlots rows repeats q otherOutside clauses designated y) :
    HEq (WholeCutSampler.collapse rows repeats p
        (CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated
          x external))
      (WholeCutSampler.collapse rows repeats q
        (CleanPhysicalCanonicalQuery.rightSlots rows repeats q otherOutside clauses designated y)
        (CleanPhysicalReplay.rightTape rows repeats q otherOutside otherPlaceholder clauses designated
          y other)) := by
  cases hp
  have hxy : x = y := eq_of_heq hx
  cases hxy
  exact SourcePhysicalExteriorReplay.collapsedTape_heq rows repeats p
    outside otherOutside placeholder otherPlaceholder
    (CleanPhysicalReplay.rightInside rows repeats p clauses designated x)
    hslots external other hext (CleanPhysicalReplay.rightBlocks rows repeats p clauses designated x)

private theorem joinedExterior_heq
    (p : Path branch root (h + 1))
    (inside : PreliminarySampler.Questions branch (h + 1) t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m)
    (exterior : SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external) :
    HEq (@Equiv.toFun
      (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external)
      (SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p
        (SourceQuestionCutSplit.join p inside external))
      (SourcePhysicalSourceSwap.joinedExterior clauses rows repeats p inside external) exterior)
      exterior := by
  exact cast_trans_toFun_heq
    (congrArg (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p)
      (SourcePhysicalSourceSwap.outside_join p inside external).symm)
    (SourcePhysicalExteriorSwap.fromCanonical clauses rows repeats p
      (SourceQuestionCutSplit.join p inside external))
    (SourcePhysicalExteriorSwap.fromCanonical_heq clauses rows repeats p
      (SourceQuestionCutSplit.join p inside external)) exterior

end Transport

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)
  (sample : FixedStoppedNativeLaw.Sample parameters i j hij input)

local notation "R" => FixedRows.rows parameters.plan
local notation "T" => FixedRows.repeats parameters.plan
local notation "C" => clauses input
local notation "D" => designated parameters i
local notation "hu" => Nat.succ_le_of_lt j.isLt
local notation "P" => physicalSample parameters i j hij input sample
local notation "K" => innerTag parameters i j hij input sample
local notation "S" => FixedStoppedNativeLaw.setup parameters i j hij input (Sigma.fst sample)

abbrev physicalRead :=
  StoppedProjectedExperiment.physicalRead C R T hu hij D P.1 P.2.1

abbrev experimentRead :=
  StoppedProjectedExperiment.physicalExperimentRead C R T hu hij D P.1 P.2.1

abbrev rawRead :=
  StoppedProjectedPhysicalAdvice.read C R T hu hij D parameters.plan.order P

private theorem exterior_heq : HEq (S).exterior P.2.1.2.1 := by
  have hclean : HEq (S).exterior sample.1.2.2.2.2 := by
    have hfilled : HEq
        (StoppedCleanGeometry.filledExteriorEquiv parameters input
          (FixedStoppedDecoderContext.upperPath parameters i j sample.1.1)
          (FixedStoppedDecoderContext.lowerPath parameters i j hij sample.1.1)
          sample.1.2.1 sample.1.2.2.2.2) sample.1.2.2.2.2 := cast_heq _ _
    exact (cast_heq _ _).trans hfilled
  have hphysical : HEq P.2.1.2.1 sample.1.2.2.2.2 := by
    exact joinedExterior_heq R T C
      (path parameters i j hij input sample)
      (SourceQuestionRawSwap.insideQuestions R C D (childSample parameters i j hij input sample))
      sample.1.2.1 sample.1.2.2.2.2
  exact hclean.trans hphysical.symm

theorem physicalRead_tape_heq :
    HEq (physicalRead parameters i j hij input sample).2
      (CleanPhysicalDecoderLaw.rightWholeTape S sample.2) := by
  have hphysical := observeFiber_tape_heq R T C D
    (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots C P.1)
    (SourceProjectedTag.originalSlots C
      (StoppedProjectedExperiment.cutQuestions R hu hij P.1
        (StoppedProjectedExperiment.baseTag R P.2.1.1)))
    (StoppedProjectedExperiment.physicalSources R hu hij D P.1 P.2.1.1)
    (childSample parameters i j hij input sample)
    (FixedStoppedNativeProjection.physicalSources_eq parameters i j hij input sample)
    P.2.1.2.1
  have hchild : HEq sample.2 (childSample parameters i j hij input sample) :=
    (cast_heq _ _).symm
  have hclean := collapsedRightTape_heq R T C D
    (FixedStoppedNativeLaw.path_eq parameters i j hij input sample.1)
    (S).outside (StoppedProjectedExperiment.nativeSlots C P.1)
    (S).placeholder
    (SourceProjectedTag.originalSlots C
      (StoppedProjectedExperiment.cutQuestions R hu hij P.1
        (StoppedProjectedExperiment.baseTag R P.2.1.1)))
    sample.2 (childSample parameters i j hij input sample) hchild
    (S).exterior P.2.1.2.1 (exterior_heq parameters i j hij input sample)
    ((FixedStoppedNativeProjection.rightSlots_eq parameters i j hij input sample).trans
      (FixedStoppedNativeProjection.physicalRightSlots_eq parameters i j hij input sample))
  exact hphysical.trans hclean.symm

theorem experimentTape_heq :
    HEq (experimentRead parameters i j hij input sample).2
      (CleanPhysicalDecoderLaw.uncastTape (CleanNativeReplay.rightSlots S sample.2)
        (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
        (CleanPhysicalDecoderLaw.lower S) (S).cut
        (CleanDecoderContext.lowerHeight
          (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
          (FixedStoppedDecoderContext.lowerIndex parameters i j hij input sample.1))
        (CleanPhysicalDecoderLaw.rightWholeTape S sample.2)) := by
  have hphysical := StoppedCleanOwnInputGeometry.pathTapeEquiv_heq R T
    (StoppedProjectedExperiment.projectedSlots C R hu hij D P.1 K)
    (StoppedProjectedExperiment.fullPath_spec R hu hij P.1 K).symm
    (physicalRead parameters i j hij input sample).2
  have hclean := StoppedCleanOwnInputGeometry.uncastTape_heq R T
    (CleanNativeReplay.rightSlots S sample.2)
    (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
    (CleanPhysicalDecoderLaw.lower S) (S).cut
    (CleanDecoderContext.lowerHeight
      (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
      (FixedStoppedDecoderContext.lowerIndex parameters i j hij input sample.1))
    (CleanPhysicalDecoderLaw.rightWholeTape S sample.2)
  exact hphysical.trans ((physicalRead_tape_heq parameters i j hij input sample).trans hclean.symm)

theorem rawSample_heq :
    HEq (rawRead parameters i j hij input sample).2.2.2
      (CleanPhysicalProjectedMeeting.rawSample S
        (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
        sample.2) :=
  StoppedCleanOwnInputGeometry.exposedRead_heq R T
    (StoppedProjectedExperiment.projectedSlots C R hu hij D P.1 K)
    (CleanNativeReplay.rightSlots S sample.2)
    (FixedStoppedNativeProjection.rightSlots_eq parameters i j hij input sample).symm
    (StoppedProjectedExperiment.upper hu P.1)
    (StoppedProjectedExperiment.lower R hu hij P.1 K) (CleanPhysicalDecoderLaw.lower S)
    (StoppedCleanCutEquality.stopped_lower_eq R hu hij P.1 K)
    (StoppedProjectedExperiment.cut R hu hij P.1 K) (S).cut
    (StoppedCleanCutEquality.stopped_cut_heq R hu hij P.1 K)
    (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
    (experimentRead parameters i j hij input sample).2 _
    (experimentTape_heq parameters i j hij input sample)

theorem visible_heq :
    HEq (rawRead parameters i j hij input sample).2.2.2.2
      (CleanPhysicalProjectedMeeting.visible S
        (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
        sample.2) :=
  StoppedCleanOwnInputGeometry.visibleRead_heq R T
    (StoppedProjectedExperiment.projectedSlots C R hu hij D P.1 K)
    (CleanNativeReplay.rightSlots S sample.2)
    (FixedStoppedNativeProjection.rightSlots_eq parameters i j hij input sample).symm
    (StoppedProjectedExperiment.upper hu P.1)
    (StoppedProjectedExperiment.lower R hu hij P.1 K) (CleanPhysicalDecoderLaw.lower S)
    (StoppedCleanCutEquality.stopped_lower_eq R hu hij P.1 K)
    (StoppedProjectedExperiment.cut R hu hij P.1 K) (S).cut
    (StoppedCleanCutEquality.stopped_cut_heq R hu hij P.1 K)
    (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
    (experimentRead parameters i j hij input sample).2 _
    (experimentTape_heq parameters i j hij input sample)

end
end PerfectCompleteness.FixedStoppedNativeTape

end

end OAI
