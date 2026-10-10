import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionRawSwap
import OAI.Computability.PerfectCompleteness.Decoding.SourceChildProjectionComparison
import OAI.Computability.PerfectCompleteness.Foundations.SourcePhysicalExteriorSwap
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SourcePhysicalWholeLaw

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalSourceSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (designated : Fin (branch h) → Slots branch h)

abbrev Questions := PreliminarySampler.Questions branch root t m
abbrev Positions := SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := h) (t := t)
abbrev Raw := SourceChildKernelJoint.RawTuple (C := WholeCutCalls.Index rows repeats p)
  (t := t) rows clauses designated
abbrev ChildSample := SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p)
  (t := t) rows clauses designated

omit [NeZero m] in
@[simp] theorem outside_join
    (inside : PreliminarySampler.Questions branch (h + 1) t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m) :
    SourceQuestionCutSplit.outside p (SourceQuestionCutSplit.join p inside external) = external := by
  funext leaf
  exact SourceQuestionCutSplit.join_outside p inside external leaf

def joinedExterior
    (inside : PreliminarySampler.Questions branch (h + 1) t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m) :
    SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external ≃
      SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p
        (SourceQuestionCutSplit.join p inside external) :=
  (Equiv.cast (congrArg (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p)
    (outside_join p inside external).symm)).trans
      (SourcePhysicalExteriorSwap.fromCanonical clauses rows repeats p
        (SourceQuestionCutSplit.join p inside external))

theorem joinedExterior_law
    (inside : PreliminarySampler.Questions branch (h + 1) t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m) :
    (FiniteDistribution.uniform
      (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external)).pushforward
        (joinedExterior clauses rows repeats p inside external) =
      FiniteDistribution.uniform (SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p
        (SourceQuestionCutSplit.join p inside external)) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (joinedExterior clauses rows repeats p inside external)

theorem expectation_joinedExterior
    (inside : PreliminarySampler.Questions branch (h + 1) t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m)
    (value : SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p
      (SourceQuestionCutSplit.join p inside external) → ℝ) :
    (FiniteDistribution.uniform (SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p
      (SourceQuestionCutSplit.join p inside external))).expectation value =
      (FiniteDistribution.uniform
        (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external)).expectation
          (fun exterior => value (joinedExterior clauses rows repeats p inside external exterior)) := by
  rw [← joinedExterior_law clauses rows repeats p inside external,
    FiniteDistribution.expectation_pushforward]

theorem expectation_swap
    (flag : Fin (branch h) → FiniteDistribution Bool)
    (value : (questions : Questions (branch := branch) (root := root) (t := t) (m := m)) →
      Positions (branch := branch) (h := h) (t := t) →
      SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p questions →
      Raw clauses rows repeats p designated → ℝ) :
    (PreliminarySampler.questionsLaw
      (branch := branch) (n := root) (t := t) (m := m)).expectation
        (fun questions => (SourceProjectedTag.positionLaw
          (branch := branch) (n := h) (t := t)).expectation (fun positions =>
            (SourcePhysicalWholeLaw.rawLaw rows repeats p
              (sourceSlots clauses (PreliminarySampler.endpoints questions))
              (sourceSlots clauses (PreliminarySampler.endpoints
                (SourceQuestionCutSplit.restrict p questions)))
              clauses designated flag (SourceQuestionKernelJoint.sources designated
                (SourceQuestionCutSplit.restrict p questions) positions)).expectation
                  (fun sample => value questions positions sample.1 sample.2))) =
      (FiniteDistribution.uniform (SourceQuestionCutSplit.OutsideQuestions p t m)).expectation
        (fun external => (FiniteDistribution.uniform
          (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external)).expectation
            (fun exterior => (SourceChildKernel.originalLaw
              (C := WholeCutCalls.Index rows repeats p) (t := t)
              rows clauses designated flag).expectation (fun sample =>
                value (SourceQuestionCutSplit.join p
                    (SourceQuestionRawSwap.insideQuestions rows clauses designated sample) external)
                  (SourceQuestionRawSwap.positions rows clauses designated sample)
                  (joinedExterior clauses rows repeats p
                    (SourceQuestionRawSwap.insideQuestions rows clauses designated sample)
                    external exterior)
                  (SourceQuestionRawSwap.raw rows clauses designated sample)))) := by
  let statistic := fun (questions : Questions (branch := branch) (root := root) (t := t) (m := m))
      (positions : Positions (branch := branch) (h := h) (t := t))
      (raw : Raw clauses rows repeats p designated) =>
    (FiniteDistribution.uniform
      (SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p questions)).expectation
        (fun external => value questions positions external raw)
  calc
    _ = (PreliminarySampler.questionsLaw
        (branch := branch) (n := root) (t := t) (m := m)).expectation
          (fun questions => (SourceProjectedTag.positionLaw
            (branch := branch) (n := h) (t := t)).expectation (fun positions =>
              (SourceQuestionRawSwap.kernelLaw rows clauses designated flag
                (SourceQuestionCutSplit.restrict p questions) positions).expectation
                  (statistic questions positions))) := by
      apply FiniteDistribution.expectation_congr
      intro questions
      apply FiniteDistribution.expectation_congr
      intro positions
      rw [SourcePhysicalWholeLaw.rawLaw, FiniteDistribution.expectation_product]
      exact FiniteDistribution.expectation_comm _ _ _
    _ = (FiniteDistribution.uniform (SourceQuestionCutSplit.OutsideQuestions p t m)).expectation
        (fun external => (SourceChildKernel.originalLaw
          (C := WholeCutCalls.Index rows repeats p) (t := t)
          rows clauses designated flag).expectation (fun sample =>
            statistic (SourceQuestionCutSplit.join p
                (SourceQuestionRawSwap.insideQuestions rows clauses designated sample) external)
              (SourceQuestionRawSwap.positions rows clauses designated sample)
              (SourceQuestionRawSwap.raw rows clauses designated sample))) :=
      SourceQuestionRawSwap.fullQuestions_expectation rows clauses designated flag p statistic
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro external
      calc
        _ = (SourceChildKernel.originalLaw (C := WholeCutCalls.Index rows repeats p) (t := t)
            rows clauses designated flag).expectation (fun sample =>
              (FiniteDistribution.uniform
                (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external)).expectation
                  (fun exterior => value (SourceQuestionCutSplit.join p
                      (SourceQuestionRawSwap.insideQuestions rows clauses designated sample) external)
                    (SourceQuestionRawSwap.positions rows clauses designated sample)
                    (joinedExterior clauses rows repeats p
                      (SourceQuestionRawSwap.insideQuestions rows clauses designated sample)
                      external exterior)
                    (SourceQuestionRawSwap.raw rows clauses designated sample))) := by
          apply FiniteDistribution.expectation_congr
          intro sample
          exact expectation_joinedExterior clauses rows repeats p
            (SourceQuestionRawSwap.insideQuestions rows clauses designated sample) external _
        _ = _ := FiniteDistribution.expectation_comm _ _ _

end
end PerfectCompleteness.SourcePhysicalSourceSwap

end

section

namespace PerfectCompleteness.SourcePhysicalStoppedComparison

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t v m : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Sources := SourceChildKernel.Sources (m := m) (t := t) designated

abbrev NativeArrays (sources : Sources (m := m) (t := t) designated) :=
  Arrays (CutSlotAssembly.fill p outside
    (SourceChildKernel.parentLeftSlots clauses designated sources)) rows

def modifiedLaw (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (sources : Sources (m := m) (t := t) designated) :
    FiniteDistribution (NativeArrays rows p outside clauses designated sources) :=
  (SourcePhysicalWholeLaw.rawLaw rows repeats p outside placeholder clauses designated
    (fun _ => ProjectionPosterior.bernoulli β hβ hβ') sources).pushforward
      (SourcePhysicalWholeLaw.observeLeft rows repeats p outside placeholder clauses designated sources)

def stoppedLaw (sources : Sources (m := m) (t := t) designated) :
    FiniteDistribution (NativeArrays rows p outside clauses designated sources) :=
  WholeArraySampler.law rows repeats p
    (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources))

theorem conditional_variation (hbranch : 0 < branch h)
    (sources : Sources (m := m) (t := t) designated) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (modifiedLaw rows repeats p outside placeholder clauses designated β hβ hβ' sources).totalVariation
      (stoppedLaw rows repeats p outside clauses designated sources) ≤
      SourceChildProjectionComparison.error branch h t
        (Fintype.card (WholeCutCalls.Index rows repeats p)) rows β := by
  let μ := FiniteDistribution.uniform
    (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
  let P := SourcePhysicalWholeLaw.nativeBlockLaw rows repeats p clauses designated
    (fun _ => ProjectionPosterior.bernoulli β hβ hβ') sources
  let Q := CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p)
    (SourceChildKernel.parentLeftSlots clauses designated sources) rows
  let evaluate := fun x : CleanPhysicalReplay.Exterior rows repeats p outside placeholder ×
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (SourceChildKernel.parentLeftSlots clauses designated sources) rows =>
    WholeCutSampler.evaluate rows repeats p
      (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources))
      (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder
        (SourceChildKernel.parentLeftSlots clauses designated sources) x.1 x.2)
  have hnative : P.totalVariation Q ≤
      SourceChildProjectionComparison.error branch h t
        (Fintype.card (WholeCutCalls.Index rows repeats p)) rows β := by
    have hh := SourceChildProjectionComparison.conditional_observed_variation
      (C := WholeCutCalls.Index rows repeats p) rows clauses designated hbranch sources β hβ hβ'
      (id : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (SourceChildKernel.parentLeftSlots clauses designated sources) rows → _)
    change (P.pushforward id).totalVariation (Q.pushforward id) ≤ _ at hh
    rw [FiniteDistribution.pushforward_id P, FiniteDistribution.pushforward_id Q] at hh
    exact hh
  have hcompare := CommonProductVariation.observed_product_le_of_bound μ P Q evaluate hnative
  have hmodified : modifiedLaw rows repeats p outside placeholder clauses designated β hβ hβ' sources =
      (μ.product P).pushforward evaluate :=
    SourcePhysicalWholeLaw.observeLeft_law rows repeats p outside placeholder clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ') sources
  have hstopped : (μ.product Q).pushforward evaluate =
      stoppedLaw rows repeats p outside clauses designated sources :=
    CleanPhysicalReplayLaw.evaluate_physicalTape_law rows repeats p outside placeholder
      (SourceChildKernel.parentLeftSlots clauses designated sources)
  rw [← hmodified, hstopped] at hcompare
  exact hcompare

abbrev Observation := Σ sources : Sources (m := m) (t := t) designated,
  NativeArrays rows p outside clauses designated sources

def sourceModifiedLaw (source : FiniteDistribution (Sources (m := m) (t := t) designated))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (Observation rows p outside clauses designated) :=
  CompletionSoundness.sigmaLaw source
    (modifiedLaw rows repeats p outside placeholder clauses designated β hβ hβ')

def sourceStoppedLaw (source : FiniteDistribution (Sources (m := m) (t := t) designated)) :
    FiniteDistribution (Observation rows p outside clauses designated) :=
  CompletionSoundness.sigmaLaw source (stoppedLaw rows repeats p outside clauses designated)

theorem source_variation (source : FiniteDistribution (Sources (m := m) (t := t) designated))
    (hbranch : 0 < branch h) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (sourceModifiedLaw rows repeats p outside placeholder clauses designated source β hβ hβ').totalVariation
      (sourceStoppedLaw rows repeats p outside clauses designated source) ≤
      SourceChildProjectionComparison.error branch h t
        (Fintype.card (WholeCutCalls.Index rows repeats p)) rows β := by
  rw [sourceModifiedLaw, sourceStoppedLaw, ConditionalVariation.sigma_totalVariation]
  apply (SmallBias.expectation_mono source
    (fun sources => conditional_variation rows repeats p outside placeholder clauses designated
      hbranch sources β hβ hβ')).trans_eq
  exact SmallBias.expectation_const source _

theorem probability_ge_sub (source : FiniteDistribution (Sources (m := m) (t := t) designated))
    (hbranch : 0 < branch h) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (event : Observation rows p outside clauses designated → Bool) :
    (sourceStoppedLaw rows repeats p outside clauses designated source).probability event -
        SourceChildProjectionComparison.error branch h t
          (Fintype.card (WholeCutCalls.Index rows repeats p)) rows β ≤
      (sourceModifiedLaw rows repeats p outside placeholder clauses designated source β hβ hβ').probability
        event := by
  have htv := source_variation rows repeats p outside placeholder clauses designated
    source hbranch β hβ hβ'
  have hp := FiniteDistribution.probability_le_add_totalVariation
    (sourceStoppedLaw rows repeats p outside clauses designated source)
    (sourceModifiedLaw rows repeats p outside placeholder clauses designated source β hβ hβ') event
  rw [FiniteDistribution.totalVariation_comm] at hp
  linarith

end
end PerfectCompleteness.SourcePhysicalStoppedComparison

end

end OAI
