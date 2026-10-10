import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionCutSplit
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalReplay
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalExteriorSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))

def placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  sourceSlots clauses (PreliminarySampler.endpoints (fun _ _ => (0 : Fin m)))

def canonicalSlots (external : SourceQuestionCutSplit.OutsideQuestions p t m) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  sourceSlots clauses (PreliminarySampler.endpoints
    (SourceQuestionCutSplit.join p (fun _ _ => (0 : Fin m)) external))

abbrev CanonicalExterior (external : SourceQuestionCutSplit.OutsideQuestions p t m) :=
  WholeCutGrouping.Exterior rows repeats p (canonicalSlots clauses p external)

abbrev ActualExterior (questions : PreliminarySampler.Questions branch root t m) :=
  CleanPhysicalReplay.Exterior rows repeats p
    (sourceSlots clauses (PreliminarySampler.endpoints questions))
    (sourceSlots clauses (PreliminarySampler.endpoints
      (SourceQuestionCutSplit.restrict p questions)))

theorem canonicalSlots_outside
    (external : SourceQuestionCutSplit.OutsideQuestions p t m)
    (leaf : SourceQuestionCutSplit.OutsideLeaf p) :
    canonicalSlots clauses p external leaf.val =
      fun coordinate => SourceKeys.slot clauses (.clause (external leaf coordinate)) := by
  funext coordinate
  change SourceKeys.slot clauses (.clause
    (SourceQuestionCutSplit.join p (fun _ _ => (0 : Fin m)) external leaf.val coordinate)) = _
  rw [SourceQuestionCutSplit.join_outside]

theorem exteriorSlots_eq
    (questions : PreliminarySampler.Questions branch root t m)
    (leaf : Slots branch root) (hleaf : WholeCutExteriorTransport.Outside p leaf) :
    CutSlotAssembly.fill p
        (sourceSlots clauses (PreliminarySampler.endpoints questions))
        (sourceSlots clauses (PreliminarySampler.endpoints
          (SourceQuestionCutSplit.restrict p questions))) leaf =
      canonicalSlots clauses p (SourceQuestionCutSplit.outside p questions) leaf := by
  rw [CutSlotAssembly.fill_outside p _ _ leaf hleaf]
  exact (canonicalSlots_outside clauses p
    (SourceQuestionCutSplit.outside p questions) ⟨leaf, hleaf⟩).symm

def toCanonical (questions : PreliminarySampler.Questions branch root t m) :
    ActualExterior clauses rows repeats p questions ≃
      CanonicalExterior clauses rows repeats p (SourceQuestionCutSplit.outside p questions) :=
  WholeCutExteriorTransport.equiv rows repeats p _ _
    (exteriorSlots_eq clauses p questions)

def fromCanonical (questions : PreliminarySampler.Questions branch root t m) :
    CanonicalExterior clauses rows repeats p (SourceQuestionCutSplit.outside p questions) ≃
      ActualExterior clauses rows repeats p questions :=
  (toCanonical clauses rows repeats p questions).symm

theorem toCanonical_heq (questions : PreliminarySampler.Questions branch root t m)
    (external : ActualExterior clauses rows repeats p questions) :
    HEq (toCanonical clauses rows repeats p questions external) external :=
  cast_heq _ _

theorem fromCanonical_heq (questions : PreliminarySampler.Questions branch root t m)
    (external : CanonicalExterior clauses rows repeats p
      (SourceQuestionCutSplit.outside p questions)) :
    HEq (fromCanonical clauses rows repeats p questions external) external := by
  exact (toCanonical_heq clauses rows repeats p questions
    (fromCanonical clauses rows repeats p questions external)).symm.trans
      (heq_of_eq ((toCanonical clauses rows repeats p questions).apply_symm_apply external))

theorem toCanonical_law (questions : PreliminarySampler.Questions branch root t m) :
    (FiniteDistribution.uniform (ActualExterior clauses rows repeats p questions)).pushforward
        (toCanonical clauses rows repeats p questions) =
      FiniteDistribution.uniform (CanonicalExterior clauses rows repeats p
        (SourceQuestionCutSplit.outside p questions)) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (toCanonical clauses rows repeats p questions)

theorem fromCanonical_law (questions : PreliminarySampler.Questions branch root t m) :
    (FiniteDistribution.uniform (CanonicalExterior clauses rows repeats p
      (SourceQuestionCutSplit.outside p questions))).pushforward
        (fromCanonical clauses rows repeats p questions) =
      FiniteDistribution.uniform (ActualExterior clauses rows repeats p questions) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (fromCanonical clauses rows repeats p questions)

theorem expectation_fromCanonical
    (questions : PreliminarySampler.Questions branch root t m)
    (value : ActualExterior clauses rows repeats p questions → ℝ) :
    (FiniteDistribution.uniform (ActualExterior clauses rows repeats p questions)).expectation value =
      (FiniteDistribution.uniform (CanonicalExterior clauses rows repeats p
        (SourceQuestionCutSplit.outside p questions))).expectation
          (fun external => value (fromCanonical clauses rows repeats p questions external)) := by
  rw [← fromCanonical_law clauses rows repeats p questions,
    FiniteDistribution.expectation_pushforward]

theorem fill_eq (questions : PreliminarySampler.Questions branch root t m)
    (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot) :
    CutSlotAssembly.fill p (sourceSlots clauses (PreliminarySampler.endpoints questions)) inside =
      CutSlotAssembly.fill p
        (canonicalSlots clauses p (SourceQuestionCutSplit.outside p questions)) inside := by
  funext leaf
  by_cases hleaf : leaf ∈ Set.range p.slotEmbedding
  · obtain ⟨s, rfl⟩ := hleaf
    rw [CutSlotAssembly.fill_at_cut, CutSlotAssembly.fill_at_cut]
  · rw [CutSlotAssembly.fill_outside p _ _ leaf hleaf,
      CutSlotAssembly.fill_outside p _ _ leaf hleaf]
    exact (canonicalSlots_outside clauses p
      (SourceQuestionCutSplit.outside p questions) ⟨leaf, hleaf⟩).symm

end
end PerfectCompleteness.SourcePhysicalExteriorSwap

end

end OAI
