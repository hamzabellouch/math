import OAI.Computability.PerfectCompleteness.Decoding.CleanPhysicalDecoderLaw
import OAI.Computability.PerfectCompleteness.Decoding.CutProjectionGeometry
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedArrays
import OAI.Computability.PerfectCompleteness.Sampling.FixedStoppedPhysicalLawLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedNativeProjection

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open FixedStoppedPhysicalLaw (clauses designated)

section PathTransport

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat)
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  {p q : Path branch root (h + 1)}

omit [NeZero m] in
theorem leftSlots_sourceSampleEquiv (hp : p = q)
    (x : SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated) :
    CleanPhysicalCanonicalQuery.leftSlots rows repeats p outside clauses designated x =
      CleanPhysicalCanonicalQuery.leftSlots rows repeats q outside clauses designated
        (FixedStoppedNativeLaw.sourceSampleEquiv rows repeats clauses designated hp x) := by
  cases hp
  rfl

omit [NeZero m] in
theorem rightSlots_sourceSampleEquiv (hp : p = q)
    (x : SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated) :
    CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated x =
      CleanPhysicalCanonicalQuery.rightSlots rows repeats q outside clauses designated
        (FixedStoppedNativeLaw.sourceSampleEquiv rows repeats clauses designated hp x) := by
  cases hp
  rfl

omit [NeZero m] in
theorem projection_sourceSampleEquiv_heq (hp : p = q)
    (x : SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated) (leaf : Slots branch root) (coordinate : Fin t) :
    HEq (CleanPhysicalCanonicalQuery.projection rows repeats p outside clauses designated x
      leaf coordinate)
      (CleanPhysicalCanonicalQuery.projection rows repeats q outside clauses designated
        (FixedStoppedNativeLaw.sourceSampleEquiv rows repeats clauses designated hp x)
        leaf coordinate) := by
  cases hp
  rfl

end PathTransport

theorem fillProjection_outsidePresentation_heq
    {branch : Nat → Nat} {root h t : Nat} (p : Path branch root h)
    (outside otherOutside : Slots branch root → Fin t → MixedSupport.Slot)
    (left right : Slots branch h → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hfillLeft : CutSlotAssembly.fill p outside left =
      CutSlotAssembly.fill p otherOutside left) (leaf : Slots branch root) (a : Fin t) :
    HEq (CutProjectionAssembly.fillProjection p outside left right q leaf a)
      (CutProjectionAssembly.fillProjection p otherOutside left right q leaf a) := by
  by_cases hin : leaf ∈ Set.range p.slotEmbedding
  · obtain ⟨s, rfl⟩ := hin
    exact (CutProjectionAssembly.fillProjection_at_cut p outside left right q s a).trans
      (CutProjectionAssembly.fillProjection_at_cut p otherOutside left right q s a).symm
  · have hkeep (s u : MixedSupport.Slot) (hsu : s = u) :
        HEq (MixedSupport.Projection.keep s) (MixedSupport.Projection.keep u) := by
      cases hsu
      rfl
    exact (CutProjectionGeometry.fillProjection_outside p outside left right q leaf hin a).trans
      ((hkeep _ _ (congrFun (congrFun hfillLeft leaf) a)).trans
        (CutProjectionGeometry.fillProjection_outside p otherOutside left right q leaf hin a).symm)

private theorem fullProjection_sources_heq
    {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
    (p : Path branch root (h + 1))
    (outside : Slots branch root → Fin t → MixedSupport.Slot)
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch h) → Slots branch h)
    {sources other : SourceChildKernel.Sources (m := m) (t := t) designated}
    (hsources : sources = other) (flags : Fin (branch h) → Bool)
    (leaf : Slots branch root) (a : Fin t) :
    HEq (SourcePhysicalTapeLaw.fullProjection p outside clauses designated (sources, flags) leaf a)
      (SourcePhysicalTapeLaw.fullProjection p outside clauses designated (other, flags) leaf a) := by
  cases hsources
  rfl

private theorem projection_function_heq
    {branch : Nat → Nat} {n t : Nat}
    {left left' right right' : Slots branch n → Fin t → MixedSupport.Slot}
    (hl : left = left') (hr : right = right')
    (p : ∀ leaf a, MixedSupport.Projection (left leaf a) (right leaf a))
    (q : ∀ leaf a, MixedSupport.Projection (left' leaf a) (right' leaf a))
    (hpq : ∀ leaf a, HEq (p leaf a) (q leaf a)) : HEq p q := by
  cases hl
  cases hr
  exact heq_of_eq (funext (fun leaf => funext (fun a => eq_of_heq (hpq leaf a))))

private theorem projectedSlots_physicalRead_eq
    {branch : Nat → Nat} {n i j t v m : Nat} [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
    (designated : Fin (branch i) → Slots branch i)
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :
    StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
        (StoppedProjectedExperiment.physicalRead clauses rows repeats hupper hij designated o sample).1 =
      SourcePhysicalTapeLaw.projectedSlots
        (StoppedProjectedExperiment.stoppedPath rows hupper hij o
          (StoppedProjectedExperiment.baseTag rows sample.1))
        (StoppedProjectedExperiment.nativeSlots clauses o) clauses designated
        (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1,
          (StoppedProjectedExperiment.physicalRead
            clauses rows repeats hupper hij designated o sample).1.2.1.2) := rfl

private theorem projectedSlots_tag_eq_rightSlots
    {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
    (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
    (outside : Slots branch root → Fin t → MixedSupport.Slot)
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch h) → Slots branch h)
    (sample : SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated) :
    SourcePhysicalTapeLaw.projectedSlots p outside clauses designated
        (SourcePhysicalTapeLaw.tag rows repeats p clauses designated sample) =
      CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated sample := rfl

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev physicalSample (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  FixedStoppedNativeLaw.read parameters i j hij input sample

abbrev innerTag (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  (StoppedProjectedExperiment.physicalRead (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (physicalSample parameters i j hij input sample).1
    (physicalSample parameters i j hij input sample).2.1).1

abbrev originalQuestions (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  (physicalSample parameters i j hij input sample).1.1

abbrev path (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  FixedStoppedPhysicalLaw.path parameters i j hij sample.1.1

abbrev childSample (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  FixedStoppedNativeLaw.childRead parameters i j hij input sample.1 sample.2

abbrev sources (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  SourcePhysicalTapeLaw.sourceTag (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (path parameters i j hij input sample) (clauses input) (designated parameters i)
    (childSample parameters i j hij input sample)

abbrev flags (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  fun child => SourceChildKernel.rawProjected (FixedRows.rows parameters.plan)
    (clauses input) (designated parameters i) child
    ((childSample parameters i j hij input sample) child).2.2

theorem physicalSources_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    StoppedProjectedExperiment.physicalSources (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
      (physicalSample parameters i j hij input sample).1
      (physicalSample parameters i j hij input sample).2.1.1 =
      sources parameters i j hij input sample := by
  change SourceQuestionKernelJoint.sources (designated parameters i)
      (SourceQuestionCutSplit.restrict (path parameters i j hij input sample)
        (SourceQuestionCutSplit.join (path parameters i j hij input sample)
          (SourceQuestionRawSwap.insideQuestions (FixedRows.rows parameters.plan)
            (clauses input) (designated parameters i) (childSample parameters i j hij input sample))
          sample.1.2.1))
      (SourceQuestionRawSwap.positions (FixedRows.rows parameters.plan)
        (clauses input) (designated parameters i) (childSample parameters i j hij input sample)) = _
  have hrestrict := SourceQuestionRawSwap.restrict_join (path parameters i j hij input sample)
    (SourceQuestionRawSwap.insideQuestions (FixedRows.rows parameters.plan)
      (clauses input) (designated parameters i) (childSample parameters i j hij input sample))
    sample.1.2.1
  have hsources := congrArg (fun questions => SourceQuestionKernelJoint.sources
    (designated parameters i) questions
    (SourceQuestionRawSwap.positions (FixedRows.rows parameters.plan)
      (clauses input) (designated parameters i) (childSample parameters i j hij input sample))) hrestrict
  exact hsources.trans
    (SourceQuestionRawSwap.sources_insideQuestions_positions (FixedRows.rows parameters.plan)
      (clauses input) (designated parameters i) (childSample parameters i j hij input sample))

@[simp] theorem flags_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    (innerTag parameters i j hij input sample).2.1.2 = flags parameters i j hij input sample := rfl

theorem outside_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside =
      SourcePhysicalExteriorSwap.canonicalSlots (clauses input) (path parameters i j hij input sample)
        (SourceQuestionCutSplit.outside (path parameters i j hij input sample)
          (originalQuestions parameters i j hij input sample)) := by
  change SourcePhysicalExteriorSwap.canonicalSlots (clauses input)
      (path parameters i j hij input sample) sample.1.2.1 =
    SourcePhysicalExteriorSwap.canonicalSlots (clauses input) (path parameters i j hij input sample)
      (SourceQuestionCutSplit.outside (path parameters i j hij input sample)
        (SourceQuestionCutSplit.join (path parameters i j hij input sample) _ sample.1.2.1))
  exact (congrArg (SourcePhysicalExteriorSwap.canonicalSlots (clauses input)
      (path parameters i j hij input sample))
    (SourcePhysicalSourceSwap.outside_join (path parameters i j hij input sample)
      (SourceQuestionRawSwap.insideQuestions (FixedRows.rows parameters.plan)
        (clauses input) (designated parameters i) (childSample parameters i j hij input sample))
      sample.1.2.1)).symm

theorem fill_outside_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input)
    (inside : Slots (FixedParameters.branch parameters) (i.val + 1) →
      Fin (FixedRows.sourceLength parameters.plan hδ) → MixedSupport.Slot) :
    CutSlotAssembly.fill (path parameters i j hij input sample)
        (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside inside =
      CutSlotAssembly.fill (path parameters i j hij input sample)
        (StoppedProjectedExperiment.nativeSlots (clauses input)
          (physicalSample parameters i j hij input sample).1) inside := by
  rw [outside_eq]
  exact (SourcePhysicalExteriorSwap.fill_eq (clauses input)
    (path parameters i j hij input sample) (originalQuestions parameters i j hij input sample)
    inside).symm

theorem leftSlots_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    CleanNativeReplay.leftSlots (FixedStoppedNativeLaw.setup parameters i j hij input sample.1)
        sample.2 =
      StoppedProjectedExperiment.nativeSlots (clauses input)
        (physicalSample parameters i j hij input sample).1 := by
  have hp := leftSlots_sourceSampleEquiv (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan)
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside
    (clauses input) (designated parameters i)
    (FixedStoppedNativeLaw.path_eq parameters i j hij input sample.1) sample.2
  refine hp.trans ((fill_outside_eq parameters i j hij input sample _).trans ?_)
  exact (congrArg (SourcePhysicalTapeLaw.nativeSlots (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1) (clauses input) (designated parameters i))
    (physicalSources_eq parameters i j hij input sample)).symm.trans
      (StoppedProjectedArrays.nativeSlots_eq (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (physicalSample parameters i j hij input sample).2.1.1)

theorem physicalRightSlots_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (innerTag parameters i j hij input sample) =
      CleanPhysicalCanonicalQuery.rightSlots (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan) (path parameters i j hij input sample)
        (StoppedProjectedExperiment.nativeSlots (clauses input)
          (physicalSample parameters i j hij input sample).1)
        (clauses input) (designated parameters i) (childSample parameters i j hij input sample) := by
  have hread := projectedSlots_physicalRead_eq (clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (physicalSample parameters i j hij input sample).1
    (physicalSample parameters i j hij input sample).2.1
  have htags := congrArg₂ Prod.mk (physicalSources_eq parameters i j hij input sample)
    (flags_eq parameters i j hij input sample)
  have hslots := congrArg (SourcePhysicalTapeLaw.projectedSlots
    (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1) (clauses input) (designated parameters i)) htags
  have hright := projectedSlots_tag_eq_rightSlots (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1) (clauses input) (designated parameters i)
    (childSample parameters i j hij input sample)
  exact hread.trans (hslots.trans hright)

theorem rightSlots_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    CleanNativeReplay.rightSlots (FixedStoppedNativeLaw.setup parameters i j hij input sample.1)
        sample.2 =
      StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (innerTag parameters i j hij input sample) := by
  have hp := rightSlots_sourceSampleEquiv (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan)
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside
    (clauses input) (designated parameters i)
    (FixedStoppedNativeLaw.path_eq parameters i j hij input sample.1) sample.2
  refine hp.trans ((fill_outside_eq parameters i j hij input sample _).trans ?_)
  exact (physicalRightSlots_eq parameters i j hij input sample).symm

theorem projection_apply_heq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input)
    (leaf : Slots (FixedParameters.branch parameters) parameters.plan.depth)
    (a : Fin (FixedRows.sourceLength parameters.plan hδ)) :
    HEq (CleanPhysicalDecoderLaw.physicalProjection
      (FixedStoppedNativeLaw.setup parameters i j hij input sample.1) sample.2 leaf a)
      (StoppedProjectedExperiment.projection (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (innerTag parameters i j hij input sample) leaf a) := by
  have hp := projection_sourceSampleEquiv_heq (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan)
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside
    (clauses input) (designated parameters i)
    (FixedStoppedNativeLaw.path_eq parameters i j hij input sample.1) sample.2 leaf a
  have hout := fillProjection_outsidePresentation_heq (path parameters i j hij input sample)
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1)
    (CleanPhysicalReplay.leftInside (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (path parameters i j hij input sample) (clauses input) (designated parameters i)
      (childSample parameters i j hij input sample))
    (CleanPhysicalReplay.rightInside (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (path parameters i j hij input sample) (clauses input) (designated parameters i)
      (childSample parameters i j hij input sample))
    (SourceChildKernel.parentProjection (FixedRows.rows parameters.plan) (clauses input)
      (designated parameters i) (sources parameters i j hij input sample)
      (fun child => ((childSample parameters i j hij input sample) child).2.2))
    (fill_outside_eq parameters i j hij input sample _) leaf a
  have hs := fullProjection_sources_heq (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1) (clauses input) (designated parameters i)
    (physicalSources_eq parameters i j hij input sample).symm
    (flags parameters i j hij input sample) leaf a
  have hphysical := StoppedProjectedArrays.projection_heq (clauses input)
    (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (physicalSample parameters i j hij input sample).1
    (physicalSample parameters i j hij input sample).2.1.1
    (flags parameters i j hij input sample) leaf a
  exact hp.trans (hout.trans (hs.trans hphysical.symm))

theorem projection_heq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    HEq (CleanPhysicalDecoderLaw.physicalProjection
      (FixedStoppedNativeLaw.setup parameters i j hij input sample.1) sample.2)
      (StoppedProjectedExperiment.projection (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (innerTag parameters i j hij input sample)) :=
  projection_function_heq (leftSlots_eq parameters i j hij input sample)
    (rightSlots_eq parameters i j hij input sample) _ _
    (projection_apply_heq parameters i j hij input sample)

end
end PerfectCompleteness.FixedStoppedNativeProjection

end

end OAI
